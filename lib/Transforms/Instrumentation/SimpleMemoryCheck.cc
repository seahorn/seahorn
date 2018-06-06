#include "seahorn/Transforms/Instrumentation/SimpleMemoryCheck.hh"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

#include "avy/AvyDebug.h"
#include "sea_dsa/DsaAnalysis.hh"

#define SMC_LOG(...) LOG("smc", __VA_ARGS__)

using namespace llvm;

static llvm::cl::opt<bool>
    PrintSMCStats("print-smc-stats",
                  llvm::cl::desc("Print Simple Memory Check statistics"),
                  llvm::cl::init(false));

static llvm::cl::opt<unsigned> SMCAnalysisThreshold(
    "smc-check-threshold",
    llvm::cl::desc("Max no. of analyzed memory instructions"),
    llvm::cl::init(100));

static llvm::cl::opt<unsigned> CheckToInstrumentID(
    "smc-instrument-check",
    llvm::cl::desc("Id of the check to instrument"),
    llvm::cl::init(0));

static llvm::cl::opt<unsigned> AllocToInstrumentID(
    "smc-instrument-alloc",
    llvm::cl::desc("Id of the allocation site to instrument"),
    llvm::cl::init(0));

namespace seahorn {

struct PtrOrigin {
  llvm::Value *Ptr;
  int64_t Offset;

  void dump(llvm::raw_ostream &OS = llvm::dbgs()) const {
    OS << '<';
    if (Ptr)
      Ptr->print(OS);
    else
      OS << "nullptr";
    OS << ", " << Offset << ">\n";
  }
};

struct CheckContext {
  Instruction *MI = nullptr;
  Function *F = nullptr;
  Value *Barrier = nullptr;
  bool Collapsed = false;
  size_t AccessedBytes = 0;
  SmallVector<Value *, 8> InterestingAllocSites;
  SmallVector<Value *, 8> OtherAllocSites;

  void dump(llvm::raw_ostream &OS = llvm::dbgs()) {
    OS << "CheckContext : " << (F ? F->getName() : "nullptr") << " {\n";
    OS << "  MI: ";
    if (MI)
      MI->print(OS);
    else
      OS << " nullptr";

    OS << "\n  Barrier: ";
    if (Barrier)
      Barrier->print(OS);
    else
      OS << " nullptr";

    if (Collapsed)
      OS << " C";

    OS << "\n  AccessedBytes: " << AccessedBytes;

    OS << "\n  InterestingAllocSites: {\n";
    unsigned i = 0;
    for (auto *V : InterestingAllocSites) {
      OS << "    " << (i++) << ": ";
      V->print(OS);
      if (auto *I = dyn_cast<Instruction>(V))
        OS << "  (" << I->getFunction()->getName() << ", "
           << I->getParent()->getName() << ")";

      OS << ",\n";
    }

    unsigned Others = 0;
    OS << "  }  OtherAllocSites: {\n";
    for (auto *V : OtherAllocSites) {
      OS << "    " << (i++) << ": ";
      V->print(OS);
      if (auto *I = dyn_cast<Instruction>(V))
        OS << "  (" << I->getFunction()->getName() << ", "
           << I->getParent()->getName() << ")";

      OS << ",\n";

      const unsigned SkipOthersAfter = 8;
      if (Others++ > SkipOthersAfter) {
        OS << "...(skipping the " << (OtherAllocSites.size() - Others)
           << " remaining ones)\n";
        break;
      }
    }
    OS << "  }\n}\n";
  }
};

namespace {
// A wrapper for seahorn dsa
class SeaDsa {
  llvm::Pass *m_abc;
  sea_dsa::DsaInfo *m_dsa;

public:
  const sea_dsa::Cell *getCell(const llvm::Value *ptr,
                               const llvm::Function &fn) {
    assert(ptr);
    assert(m_dsa);

    sea_dsa::Graph *g = m_dsa->getDsaGraph(fn);
    if (!g) {
      errs() << "WARNING SMC: Sea Dsa graph not found for " << fn.getName()
             << "\n";
      return nullptr;
    }

    if (!(g->hasCell(*ptr))) {
      errs() << "WARNING SMC: Sea Dsa node not found for " << ptr << "\n";
      return nullptr;
    }

    const sea_dsa::Cell &c = g->getCell(*ptr);
    return &c;
  }

  SeaDsa(Pass *abc)
      : m_abc(abc),
        m_dsa(&this->m_abc->getAnalysis<sea_dsa::DsaInfoPass>().getDsaInfo()) {}

  SmallVector<Value *, 8> getAllocSites(Value *V, const Function &F) {
    auto *C = getCell(V, F);
    assert(C);
    auto *N = C->getNode();
    assert(N);

    SmallVector<Value *, 8> Sites;
    for (auto *S : N->getAllocSites()) {
      if (auto *GV = dyn_cast<const GlobalVariable>(S))
        if (GV->isDeclaration())
          continue;

      Sites.push_back(const_cast<Value *>(S));
    }

    return Sites;
  };

  void viewGraph(const Function &F) { m_dsa->getDsaGraph(F)->viewGraph(); }
};

} // namespace

struct TypeSimilarity;

class SimpleMemoryCheck : public llvm::ModulePass {
public:
  static char ID;
  SimpleMemoryCheck() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &M);
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;
  virtual llvm::StringRef getPassName() const { return "SimpleMemoryCheck"; }

  llvm::Optional<size_t> getAllocSize(Value *Ptr);

private:
  LLVMContext *m_Ctx;
  Module *m_M;
  CallGraph *m_CG;
  const DataLayout *m_DL;
  const TargetLibraryInfo *m_TLI;
  std::unique_ptr<SeaDsa> m_SDSA;

  Function *m_assumeFn;
  Function *m_errorFn;
  Value *m_trackedBegin;
  Value *m_trackedEnd;
  Value *m_trackingEnabled;

  bool isKnownAlloc(Value *Ptr);
  PtrOrigin trackPtrOrigin(Value *Ptr);

  using TypeSimilarityCache =
      std::map<std::pair<Type *, Type *>, TypeSimilarity>;
  CheckContext getUnsafeCandidates(Instruction *Ptr, Function &F,
                                   TypeSimilarityCache &TSC);
  bool isInterestingAllocSite(Value *Inst, int64_t LoadEnd, Value *Alloc);

  void emitGlobalInstrumentation(CheckContext &Candidate, size_t AllocId);
  void emitMemoryInstInstrumentation(CheckContext &Candidate);
  void emitAllocSiteInstrumentation(CheckContext &Candidate, size_t AllocId);

  Function *createNewNDFn(Type *Ty, Twine Prefix = "");
  CallInst *getNDVal(size_t IntBitWidth, Function *F, IRBuilder<> &IRB,
                     Twine Name = "");
  CallInst *getNDPtr(Function *F, IRBuilder<> &IRB, Twine Name = "");
  void createAssume(Value *Cond, Function *F, IRBuilder<> &IRB);

  void printStats(std::vector<CheckContext> &Checks,
                  std::vector<Instruction *> &UninterestingMIs);
};

llvm::Pass *createSimpleMemoryCheckPass() { return new SimpleMemoryCheck(); }

bool SimpleMemoryCheck::isKnownAlloc(Value *Ptr) {
  if (auto *AI = dyn_cast<AllocaInst>(Ptr))
    return !AI->isArrayAllocation();

  if (auto *CI = dyn_cast<CallInst>(Ptr))
    return isAllocationFn(CI, m_TLI);

  if (auto *GV = dyn_cast<GlobalVariable>(Ptr))
    return GV->hasInitializer();

  return false;
}

llvm::Optional<size_t> SimpleMemoryCheck::getAllocSize(Value *Ptr) {
  assert(Ptr);
  if (!isKnownAlloc(Ptr))
    return None;

  ObjectSizeOffsetEvaluator OSOE(*m_DL, m_TLI, *m_Ctx, true);
  SizeOffsetEvalType OffsetAlign = OSOE.compute(Ptr);
  if (!OSOE.knownSize(OffsetAlign))
    return llvm::None;

  if (auto *Sz = dyn_cast<ConstantInt>(OffsetAlign.first)) {
    const int64_t I = Sz->getSExtValue();
    assert(I >= 0);
    return size_t(I);
  }

  return llvm::None;
}

PtrOrigin SimpleMemoryCheck::trackPtrOrigin(Value *Ptr) {
  assert(Ptr);

  PtrOrigin Res{Ptr, 0};
  unsigned Iter = 0;
  while (true) {
    ++Iter;

    if (isKnownAlloc(Res.Ptr))
      return Res;

    if (auto *BC = dyn_cast<BitCastInst>(Res.Ptr)) {
      auto *Arg = BC->getOperand(0);
      Res.Ptr = Arg;
      continue;
    }

    if (auto *GEP = dyn_cast<GetElementPtrInst>(Res.Ptr)) {
      auto *Arg = GEP->getPointerOperand();

      APInt GEPOffset(m_DL->getPointerTypeSizeInBits(GEP->getType()), 0);
      if (!GEP->accumulateConstantOffset(*m_DL, GEPOffset))
        return Res;

      Res.Ptr = Arg;
      Res.Offset += GEPOffset.getSExtValue();
      continue;
    }

    return Res;
  }
}

static void FlattenTy(Type *ATy, LLVMContext *Ctx,
                      SmallVectorImpl<std::pair<Type *, unsigned>> &Flattened) {
  SmallVector<std::pair<Type *, unsigned>, 16> TempRes;
  SmallVector<Type *, 8> Worklist = {ATy};

  while (!Worklist.empty()) {
    auto *const Ty = Worklist.pop_back_val();

    if (Ty->isPointerTy()) {
      TempRes.push_back({Ty, 1});
      continue;
    }

    if (!isa<CompositeType>(Ty)) {
      TempRes.push_back({Ty, 1});
      continue;
    }

    if (Ty->isArrayTy()) {
      for (size_t i = 0, e = Ty->getArrayNumElements(); i != e; ++i)
        Worklist.push_back(Ty->getArrayElementType());
      continue;
    }

    if (Ty->isVectorTy()) {
      for (size_t i = 0, e = Ty->getVectorNumElements(); i != e; ++i)
        Worklist.push_back(Ty->getVectorElementType());
      continue;
    }

    assert(Ty->isStructTy());
    for (auto *SubTy : llvm::reverse(Ty->subtypes()))
      Worklist.push_back(SubTy);
  }

  // Normalize all pointer types to i8*.
  for (auto &TyNum : TempRes)
    if (TyNum.first->isPointerTy())
      TyNum.first = Type::getInt8Ty(*Ctx)->getPointerTo();

  // Merge adjacent elements of the same type.
  Flattened.push_back(TempRes.front());
  for (size_t i = 1, e = TempRes.size(); i < e; ++i) {
    if (TempRes[i].first == Flattened.back().first)
      Flattened.back().second += TempRes[i].second;
    else
      Flattened.push_back(TempRes[i]);
  }
}

struct TypeSimilarity {
  Type *First = nullptr;
  size_t FirstSize = 0;
  SmallVector<std::pair<Type *, unsigned>, 16> FlattenedFirst;
  Type *Second = nullptr;
  size_t SecondSize = 0;
  SmallVector<std::pair<Type *, unsigned>, 16> FlattenedSecond;
  unsigned MatchPosition = 0;
  unsigned NumMatching = 0;
  float Similarity = 0.0f;

  TypeSimilarity() = default;
  TypeSimilarity(const TypeSimilarity &) = default;
  TypeSimilarity &operator=(const TypeSimilarity &) = default;
  TypeSimilarity(TypeSimilarity &&) = default;
  TypeSimilarity &operator=(TypeSimilarity &&) = default;

  TypeSimilarity(Type *_First, Type *_Second, LLVMContext *Ctx,
                 const DataLayout *DL)
      : First(_First), Second(_Second), NumMatching(0) {
    FirstSize = DL->getTypeSizeInBits(First);
    SecondSize = DL->getTypeSizeInBits(Second);

    if (FirstSize > SecondSize) {
      std::swap(First, Second);
      std::swap(FirstSize, SecondSize);
    }

    FlattenTy(First, Ctx, FlattenedFirst);
    FlattenTy(Second, Ctx, FlattenedSecond);

    for (size_t k = 0, e1 = FlattenedSecond.size(); k != e1; ++k) {
      unsigned CurrentMatching = 0;

      for (size_t i = 0, e2 = FlattenedFirst.size(); i != e2 && i + k < e1;
           ++i) {
        if (FlattenedFirst[i].first == FlattenedSecond[i + k].first)
          CurrentMatching +=
              DL->getTypeSizeInBits(FlattenedFirst[i].first) *
              std::min(FlattenedFirst[i].second, FlattenedSecond[i + k].second);
        else
          break;
        if (FlattenedFirst[i].second != FlattenedSecond[i + k].second)
          break;
      }

      if (CurrentMatching > NumMatching) {
        NumMatching = CurrentMatching;
        MatchPosition = unsigned(k);
      }

      if (NumMatching == FirstSize)
        break;
    }

    Similarity = float(NumMatching) / FirstSize;
  }

  bool operator<(const TypeSimilarity &Other) const {
    return std::make_pair(First, Second) <
           std::make_pair(Other.First, Other.Second);
  }

  void dump(raw_ostream &OS = llvm::dbgs()) const {
    dumpOne(OS, "First", First, FlattenedFirst);
    dumpOne(OS, "Second", Second, FlattenedSecond);
    OS << "Similarity: " << Similarity << ", ";
    OS << "Num matching bits: " << NumMatching << "/" << FirstSize << "\n";
  }

private:
  void
  dumpOne(raw_ostream &OS, StringRef Prefix, Type *Ty,
          const SmallVectorImpl<std::pair<Type *, unsigned>> &Flattened) const {
    OS << Prefix << ":\t";
    Ty->print(OS);
    OS << "\nFlattened" << Prefix << ":\t";
    for (auto &P : Flattened) {
      OS << "[";
      P.first->print(OS);
      OS << " x " << P.second << "], ";
    }
    OS << "\n";
  }
};

CheckContext SimpleMemoryCheck::getUnsafeCandidates(Instruction *Inst,
                                                    Function &F,
                                                    TypeSimilarityCache &TSC) {
  auto *LI = dyn_cast<LoadInst>(Inst);
  auto *SI = dyn_cast<StoreInst>(Inst);
  assert((LI || SI) && "Wrong instruction type");

  Value *Arg = LI ? LI->getPointerOperand() : SI->getPointerOperand();
  assert(Arg);

  PtrOrigin Origin = trackPtrOrigin(Arg);

  auto *Ty = LI ? LI->getType()
                : SI->getPointerOperand()->getType()->getPointerElementType();
  assert(Ty);

  const auto Bits = m_DL->getTypeSizeInBits(Ty);
  const uint32_t Sz = Bits < 8 ? 1 : Bits / 8;
  const int64_t LastRead = Origin.Offset + Sz;

  CheckContext Check;
  Check.MI = Inst;
  Check.F = &F;
  Check.Barrier = Origin.Ptr;
  Check.Collapsed = m_SDSA->getCell(Origin.Ptr,
                                    F)->getNode()->isOffsetCollapsed();
  Check.AccessedBytes = size_t(LastRead);

  if (Optional<size_t> AllocSize = getAllocSize(Origin.Ptr)) {
    if (int64_t(Origin.Offset) + Sz > int64_t(*AllocSize)) {
      errs() << "Unsafe access found!\n";
      errs() << "  Allocated: " << (*AllocSize) << ", access size " << Sz
             << " at offset " << Origin.Offset << "\n";
      Check.dump(errs());
    }

    return Check;
  }

  // Assume that alloc functions return fresh memory.
  if (isAllocLikeFn(Check.Barrier, m_TLI, true))
    return Check;

  assert(Origin.Ptr);

  for (Value *AS : m_SDSA->getAllocSites(Origin.Ptr, F)) {
    if (auto *G = dyn_cast<GlobalValue>(AS))
      if (G->isDeclaration())
        continue;

    bool Interesting = isInterestingAllocSite(Origin.Ptr, LastRead, AS);

    if (Interesting /*&& Check.Collapsed*/) {
      auto *BarrierPtrTy = Check.Barrier->getType();
      auto *AllocPtrTy = AS->getType();
      if (BarrierPtrTy->isPointerTy() && AllocPtrTy->isPointerTy()) {
        auto *BarrierTy = BarrierPtrTy->getPointerElementType();
        auto *AllocTy = AllocPtrTy->getPointerElementType();

        // Temporary hack for CASS. Disabled for now.
        if (auto *Arg = dyn_cast<Argument>(Check.Barrier))
          if (false && Arg->getName() == "this")
            if (AllocTy->isStructTy() &&
                (AllocTy->getStructName().endswith("::string") ||
                 AllocTy->getStructName().endswith("::vector3")))
              Interesting = false;

        // Heap alloc tends to return i8* instead of precise type.
        if (!isa<CallInst>(AS) && !isa<InvokeInst>(AS)) {
          if (TSC.count({BarrierTy, AllocTy}) == 0)
            TSC[{BarrierTy, AllocTy}] =
                TypeSimilarity(BarrierTy, AllocTy, m_Ctx, m_DL);

          auto &TySim = TSC[{BarrierTy, AllocTy}];
//
//          if (TySim.Similarity < 0.8f)
//            Interesting = false;
//          else if (auto *Arg = dyn_cast<Argument>(Check.Barrier))
//            if (Arg->getName() == "this" && TySim.MatchPosition > 1)
//              Interesting = false;
        }

        // Discard vtables.
//        if (auto *C = dyn_cast<Constant>(AS))
//          if (C->getName().startswith("_ZTVN"))
//            Interesting = false;
      }
    }

    if (!Interesting)
      Check.OtherAllocSites.push_back(AS);
    else
      Check.InterestingAllocSites.push_back(AS);
  }

  return Check;
}

bool SimpleMemoryCheck::isInterestingAllocSite(Value *Ptr, int64_t LoadEnd,
                                               Value *Alloc) {
  assert(Ptr);
  assert(Alloc);
  assert(LoadEnd > 0);

  Optional<size_t> AllocSize = getAllocSize(Alloc);
  return AllocSize && size_t(LoadEnd) > *AllocSize;
}

namespace {

Instruction *GetNextInst(Instruction *I) {
  if (I->isTerminator())
    return I;
  return I->getParent()->getInstList().getNextNode(*I);    
}

Type *GetI8PtrTy(LLVMContext &Ctx) {
  return Type::getInt8Ty(Ctx)->getPointerTo();
}

Value *CreateIntCnst(Type *Ty, int64_t Val) {
  return ConstantInt::get(Ty, Val);
}

Value *CreateLoad(IRBuilder<> &B, Value *Ptr, const DataLayout *DL,
                  StringRef Name = "") {
  return B.CreateAlignedLoad(Ptr, DL->getABITypeAlignment(Ptr->getType()),
                             Name);
}

Value *CreateStore(IRBuilder<> &B, Value *Val, Value *Ptr,
                   const DataLayout *DL) {
  return B.CreateAlignedStore(Val, Ptr,
                              DL->getABITypeAlignment(Ptr->getType()));
}

Value *CreateNullptr(LLVMContext &Ctx) {
  return ConstantPointerNull::get(cast<PointerType>(GetI8PtrTy(Ctx)));
}

Value *CreateGlobalBool(Module &M, bool Val, Twine Name = "") {
  auto *Cnst = (Val ? ConstantInt::getTrue(M.getContext())
                    : ConstantInt::getFalse(M.getContext()));
  auto *GV = new GlobalVariable(M, Cnst->getType(), false,
                                GlobalValue::InternalLinkage, Cnst);
  GV->setName(Name);
  return GV;
}

Value *CreateGlobalPtr(Module &M, Twine Name = "") {
  auto NullPtr = cast<ConstantPointerNull>(CreateNullptr(M.getContext()));
  GlobalVariable *GV =
      new GlobalVariable(M, GetI8PtrTy(M.getContext()), false, /*non-constant*/
                         GlobalValue::InternalLinkage, NullPtr);
  GV->setName(Name);
  return GV;
}

void UpdateCallGraph(CallGraph *CG, Function *Caller, CallInst *Callee) {
  if (!CG)
    return;

  (*CG)[Caller]->addCalledFunction(CallSite(Callee),
                                   (*CG)[Callee->getCalledFunction()]);
}

} // namespace

Function *SimpleMemoryCheck::createNewNDFn(Type *Ty, Twine Name) {
  auto *Res =
      dyn_cast<Function>(m_M->getOrInsertFunction(Name.str(), Ty));
  assert(Res);

  if (m_CG)
    m_CG->getOrInsertFunction(Res);

  return Res;
}

CallInst *SimpleMemoryCheck::getNDVal(size_t Bits, Function *F,
                                      IRBuilder<> &IRB, Twine Name) {
  auto *Ty = IntegerType::get(*m_Ctx, Bits);
  auto *NondetFn = createNewNDFn(Ty, "verifier.nondet");
  CallInst *CI = IRB.CreateCall(NondetFn, None, Name);
  UpdateCallGraph(m_CG, F, CI);
  return CI;
}

CallInst *SimpleMemoryCheck::getNDPtr(Function *F, IRBuilder<> &IRB,
                                      Twine Name) {
  auto *NondetPtrFn = createNewNDFn(GetI8PtrTy(*m_Ctx), "verifier.nondet_ptr");
  CallInst *CI = IRB.CreateCall(NondetPtrFn, None, Name);
  UpdateCallGraph(m_CG, F, CI);
  return CI;
}

void SimpleMemoryCheck::createAssume(Value *Cond, Function *F,
                                     IRBuilder<> &IRB) {
  CallInst *CI = IRB.CreateCall(m_assumeFn, Cond);
  UpdateCallGraph(m_CG, F, CI);
}

/**
 * Creates 3 global variables used for pointer tracking:
 *  - tracked_begin   -- the first byte of the tracked memory chunk
 *  - tracked_end     -- one byte past the tracked memory chunk
 *  - tacking_enabled -- if the tracked memory chunk was already allocated
 *
 *  The rest of the instrumentation is emitted in the main function.
 *  We start by setting the values such that:
 *  - tracked_begin = nd_ptr(), tacked_end = nd_ptr(), tacking_enabled = false
 *  - tracked_end > tracked_begin > nullptr
 *
 *  Then we create assumptions for (not tracked) global variables:
 *  - &gv_n > tracked_end
 *
 *  If the tracked allocation site is a global variable, we also emit:
 *  - &the_gv == tracked_begin
 *  - &the_gv + sizeof(the_gv) == tracked_end
 *  - tacking_enabled = true
 */
void SimpleMemoryCheck::emitGlobalInstrumentation(CheckContext &Candidate,
                                                  size_t AllocId) {
  m_trackedBegin = CreateGlobalPtr(*m_M, "tracked_begin");
  m_trackedEnd = CreateGlobalPtr(*m_M, "tracked_end");
  m_trackingEnabled = CreateGlobalBool(*m_M, 0, "tracking_enabled");

  Function *Main = m_M->getFunction("main");
  assert(Main);

  IRBuilder<> IRB(*m_Ctx);
  IRB.SetInsertPoint(&*(Main->getEntryBlock().getFirstInsertionPt()));
  CallInst *NDPtrBegin = getNDPtr(Main, IRB, "nd_ptr_begin");
  auto *Cmp1 = IRB.CreateICmpSGT(
      NDPtrBegin,
      IRB.CreateBitOrPointerCast(CreateNullptr(*m_Ctx), NDPtrBegin->getType()));

  createAssume(Cmp1, Main, IRB);
  CreateStore(IRB, NDPtrBegin, m_trackedBegin, m_DL);

  CallInst *NDPtrEnd = getNDPtr(Main, IRB, "nd_ptr_end");
  auto *Cmp2 = IRB.CreateICmpSGT(NDPtrEnd, NDPtrBegin);
  createAssume(Cmp2, Main, IRB);
  CreateStore(IRB, NDPtrEnd, m_trackedEnd, m_DL);

  auto *TrackedAlloc = Candidate.InterestingAllocSites[AllocId];
  if (auto *TrackedGV = dyn_cast<GlobalVariable>(TrackedAlloc)) {
    assert(!TrackedGV->isDeclaration());

    auto *I8GV = IRB.CreateBitCast(TrackedGV, GetI8PtrTy(*m_Ctx));
    auto *GlobalIsBegin = IRB.CreateICmpEQ(I8GV, NDPtrBegin, "global.is.begin");
    createAssume(GlobalIsBegin, Main, IRB);

    Optional<size_t> AllocSize = getAllocSize(TrackedAlloc);
    assert(AllocSize);

    auto *GlobalEnd = IRB.CreateGEP(
        I8GV,
        CreateIntCnst(IntegerType::getInt32Ty(*m_Ctx), int64_t(*AllocSize)),
        "global_end_ptr");
    auto *EndEq = IRB.CreateICmpEQ(GlobalEnd, NDPtrEnd);
    createAssume(EndEq, Main, IRB);

    CreateStore(IRB, ConstantInt::getTrue(*m_Ctx), m_trackingEnabled, m_DL);
  } else {
    CreateStore(IRB, ConstantInt::getFalse(*m_Ctx), m_trackingEnabled, m_DL);
  }

  auto EmitOtherGVAssume = [&](Value *V) {
    auto *GV = dyn_cast<GlobalVariable>(V);
    if (!GV)
      return;

    auto *I8GV = IRB.CreateBitOrPointerCast(GV, GetI8PtrTy(*m_Ctx),
                                            GV->getName() + ".i8");
    auto *CmpGV = IRB.CreateICmpSGT(I8GV, NDPtrEnd);
    createAssume(CmpGV, Main, IRB);
  };

  for (auto *AV : Candidate.InterestingAllocSites) {
    if (AV == TrackedAlloc)
      continue;

    EmitOtherGVAssume(AV);
  }

  for (auto *AV : Candidate.OtherAllocSites)
    EmitOtherGVAssume(AV);

  // FIXME: undefined symbols llvm::Value::dump() while porting to 5.0
  //SMC_LOG(NDPtrBegin->getParent()->dump());
}

/**
 * For the selected Memory Instruction (load/store) and barrier, emits:
 *   if (tacking_enabled && barrier == tracked_begin)
 *     verifier.error()
 */
void SimpleMemoryCheck::emitMemoryInstInstrumentation(CheckContext &Candidate) {
  assert(isa<LoadInst>(Candidate.MI) || isa<StoreInst>(Candidate.MI));
  IRBuilder<> IRB(Candidate.MI);

  auto *BeginCandiate = IRB.CreateBitOrPointerCast(
      Candidate.Barrier, GetI8PtrTy(*m_Ctx), "begin_candidate");
  auto *TrackedBegin = CreateLoad(IRB, m_trackedBegin, m_DL, "tracked_begin");
  auto *Cmp = IRB.CreateICmpEQ(TrackedBegin, BeginCandiate);
  auto *Active = IRB.CreateLoad(m_trackingEnabled, "active_tracking");
  auto *And = IRB.CreateAnd(Active, Cmp, "unsafe_condition");
  auto *Term = SplitBlockAndInsertIfThen(And, Candidate.MI, true);
  IRB.SetInsertPoint(Term);
  IRB.CreateCall(m_errorFn);


  // FIXME: undefined symbols llvm::Value::dump() while porting to 5.0  
  // SMC_LOG(cast<Instruction>(Candidate.Barrier)->getParent()->dump());
  // SMC_LOG(Term->getParent()->dump());
}

/**
 * If the selected allocation site is malloc/alloca, nondeterministically
 * start tracking it, if it's not already being tracked:
 *   ptr = alloc(bytes)
 *   if (!tacking_enabled && nd() == 0) verifier.assume(ptr == tracked_begin)
 *     verifier.assume(ptr + bytes = tracked_end)
 *     tracking_enabled = true
 *
 * For other mallocs/allocas that alias with the instrumented barrier, assume
 * they produce chunks of memory we are not tracking:
 *   other_ptr = alloc(...)
 *   verifier.assume(other_ptr > tracked_end)
 */
void SimpleMemoryCheck::emitAllocSiteInstrumentation(CheckContext &Candidate,
                                                     size_t AllocId) {
  assert(Candidate.InterestingAllocSites.size() > AllocId);

  Value *const Alloc = Candidate.InterestingAllocSites[AllocId];
  IRBuilder<> IRB(*m_Ctx);

  // GlobalVariables are handles in emitGlobalInstrumentation.
  if (!isa<GlobalVariable>(Alloc)) {
    assert(isa<CallInst>(Alloc) || isa<AllocaInst>(Alloc));
    auto *AI = cast<Instruction>(Alloc);
    auto *CSFn = AI->getFunction();
    assert(CSFn);

    IRB.SetInsertPoint(GetNextInst(AI));
    auto *AllocI8 = IRB.CreateBitCast(AI, GetI8PtrTy(*m_Ctx), "alloc.i8");
    auto *Active = IRB.CreateLoad(m_trackingEnabled, "active_tracking");
    auto *NotActive = IRB.CreateICmpEQ(Active, ConstantInt::getFalse(*m_Ctx),
                                       "inactive_tracking");
    auto *NDVal = getNDVal(32, CSFn, IRB);
    auto *NDBool = IRB.CreateICmpEQ(NDVal, CreateIntCnst(NDVal->getType(), 0));
    auto *TrackedEnd = CreateLoad(IRB, m_trackedEnd, m_DL, "loaded_end");
    auto *And = dyn_cast<Instruction>(IRB.CreateAnd(NotActive, NDBool));
    assert(And);

    TerminatorInst *ThenTerm;
    TerminatorInst *ElseTerm;
    SplitBlockAndInsertIfThenElse(And, GetNextInst(And), &ThenTerm, &ElseTerm);

    auto *ThenBB = ThenTerm->getParent();
    ThenBB->setName("start_tracking");
    auto *ElseBB = ElseTerm->getParent();
    ElseBB->setName("not_tracking");

    // Continue inserting before the new branch.
    IRB.SetInsertPoint(ElseBB->getFirstNonPHI());
    auto *GT = IRB.CreateICmpSGT(AllocI8, TrackedEnd);
    createAssume(GT, CSFn, IRB);

    // Start tracking.
    IRB.SetInsertPoint(ThenBB->getFirstNonPHI());
    CreateStore(IRB, ConstantInt::getTrue(*m_Ctx), m_trackingEnabled, m_DL);
    auto *TrackedBegin = CreateLoad(IRB, m_trackedBegin, m_DL, "loaded_begin");
    auto *AllocIsBegin =
        IRB.CreateICmpEQ(AllocI8, TrackedBegin, "alloc.is.begin");
    createAssume(AllocIsBegin, CSFn, IRB);

    Optional<size_t> AllocSize = getAllocSize(AI);
    assert(AllocSize);

    auto *End = IRB.CreateGEP(
        AllocI8,
        CreateIntCnst(IntegerType::getInt32Ty(*m_Ctx), int64_t(*AllocSize)),
        "end_ptr");
    auto *EndEq = IRB.CreateICmpEQ(End, TrackedEnd);
    createAssume(EndEq, CSFn, IRB);
  }

  auto InstrumentRemainingSite = [&](Value *AV) {
    // Remaining GlobalVariables are handled in emitGlobalInstrumentation.
    if (isa<GlobalVariable>(AV))
      return;

    assert(isa<Instruction>(AV));
    auto *OtherAllocInst = cast<Instruction>(AV);
    IRB.SetInsertPoint(GetNextInst(OtherAllocInst));
    auto *OAI8 =
        IRB.CreateBitCast(OtherAllocInst, GetI8PtrTy(*m_Ctx), "other.alloc.i8");
    auto *TrackedEnd = CreateLoad(IRB, m_trackedEnd, m_DL, "loaded_end");
    auto *GT = IRB.CreateICmpSGT(OAI8, TrackedEnd);
    createAssume(GT, OtherAllocInst->getFunction(), IRB);

    SMC_LOG(dbgs() << "Instrumented other alloc site for " << AV->getName()
                   << ":\n");
    // FIXME: undefined symbols llvm::Value::dump() while porting to 5.0  
    //SMC_LOG(OtherAllocInst->getParent()->dump());
  };

  for (size_t i = 0; i < Candidate.InterestingAllocSites.size(); ++i) {
    if (i == AllocId)
      continue;

    auto *AV = Candidate.InterestingAllocSites[i];
    InstrumentRemainingSite(AV);
  }

  for (auto *AV : Candidate.OtherAllocSites)
    InstrumentRemainingSite(AV);
}

bool SimpleMemoryCheck::runOnModule(llvm::Module &M) {
  if (M.begin() == M.end())
    return false;

  Function *main = M.getFunction("main");
  if (!main) {
    errs() << "Main not found: no buffer overflow checks added\n";
    return false;
  }

  m_Ctx = &M.getContext();
  m_M = &M;
  m_TLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
  m_DL = &M.getDataLayout();
  m_SDSA = llvm::make_unique<SeaDsa>(this);

  SMC_LOG(dbgs() << "\n\n ========== SMC  ==========\n");
 // SMC_LOG(m_SDSA->viewGraph(*main));

  AttrBuilder AB;
  AB.addAttribute(Attribute::NoReturn);
  AttributeList AS = AttributeList::get(*m_Ctx, AttributeList::FunctionIndex, AB);
  m_errorFn = dyn_cast<Function>(M.getOrInsertFunction(
      "verifier.error", AS, Type::getVoidTy(*m_Ctx)));

  AB.clear();
  AS = AttributeList::get(*m_Ctx, AttributeList::FunctionIndex, AB);
  m_assumeFn = dyn_cast<Function>(
      M.getOrInsertFunction("verifier.assume", AS, Type::getVoidTy(*m_Ctx),
                            Type::getInt1Ty(*m_Ctx)));

  IRBuilder<> B(*m_Ctx);
  CallGraphWrapperPass *CGWP = getAnalysisIfAvailable<CallGraphWrapperPass>();
  m_CG = CGWP ? &CGWP->getCallGraph() : nullptr;
  if (m_CG) {
    m_CG->getOrInsertFunction(m_assumeFn);
    m_CG->getOrInsertFunction(m_errorFn);
  }

  std::vector<CheckContext> CheckCandidates;
  std::vector<Instruction *> UninterestingMIs;

  TypeSimilarityCache TSC;

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;

    // Skip special functions.
    if (F.getName().startswith("seahorn.") ||
        F.getName().startswith("shadow.") ||
        F.getName().startswith("verifier."))
      continue;

    for (auto &BB : F) {
      for (auto &V : BB) {
        auto *I = dyn_cast<Instruction>(&V);
        if (I && (isa<LoadInst>(I) || isa<StoreInst>(I))) {

          CheckContext Check = getUnsafeCandidates(I, F, TSC);

          // Skip collapsed DSA nodes for now, as they generate too much
          // noise.
//          if (Check.InterestingAllocSites.empty() /*|| Check.Collapsed*/) {
//            UninterestingMIs.push_back(I);
//            continue;
//          }

          CheckCandidates.emplace_back(std::move(Check));

          SMC_LOG(dbgs() << (CheckCandidates.size() - 1) << ": ");
          SMC_LOG(CheckCandidates.back().dump());

          if (CheckCandidates.size() >= SMCAnalysisThreshold) {
            SMC_LOG(errs() << "Skipping SMC analysis after reaching the"
                              " threshold of"
                           << SMCAnalysisThreshold.getValue() << "\n");
            goto skip;
          }
        }
      }
    }
  }

skip:

  if (PrintSMCStats) {
    printStats(CheckCandidates, UninterestingMIs);

    dbgs() << "\n~~~~~~  TypeSimilarityCache  ~~~~~~\n";

    std::vector<TypeSimilarity> TySims;
    TySims.reserve(TSC.size());
    for (auto &TyTySim : TSC)
      TySims.push_back(TyTySim.second);
    std::sort(TySims.begin(), TySims.end(),
              [](const TypeSimilarity &A, const TypeSimilarity &B) {
                return std::make_pair(A.Similarity, A.NumMatching) >
                       std::make_pair(B.Similarity, B.NumMatching);
              });

    unsigned i = 0;
    for (auto &TySim : TySims) {
      if (TySim.Similarity < 0.8f)
        break;
      dbgs() << "\n" << (i++) << ":\n";
      TySim.dump(dbgs());
    }

    return false;
  }

  if (CheckCandidates.empty()) {
    SMC_LOG(dbgs() << "No check candidates!\n");
    return true;
  }

  size_t CheckId = CheckToInstrumentID;
  size_t AllocSiteId = AllocToInstrumentID;

  assert(CheckCandidates.size() > CheckId);
  auto &Check = CheckCandidates[CheckId];
  SMC_LOG(dbgs() << "Emitting instrumentation for check [" << CheckId
                 << "], alloc (" << AllocSiteId << ")\n");
  SMC_LOG(Check.dump());

  emitGlobalInstrumentation(Check, AllocSiteId);
  emitMemoryInstInstrumentation(Check);
  emitAllocSiteInstrumentation(Check, AllocSiteId);

  // SMC_LOG(M.dump());

  SMC_LOG(dbgs() << " ========== SMC  ==========\n");
  return true;
}

void SimpleMemoryCheck::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<sea_dsa::DsaInfoPass>(); // run seahorn dsa
  AU.addRequired<llvm::TargetLibraryInfoWrapperPass>();
  AU.addRequired<llvm::UnifyFunctionExitNodes>();
  AU.addRequired<llvm::CallGraphWrapperPass>();
  // for debugging
  // AU.addRequired<ufo::NameValues> ();
}

template <typename ValTy, typename Container>
static size_t CountOfType(const Container &C) {
  size_t Res = 0;
  for (auto *V : C)
    if (isa<ValTy>(V))
      ++Res;

  return Res;
};

template <typename Container> static size_t CountOfHeap(const Container &C) {
  return CountOfType<CallInst>(C) + CountOfType<InvokeInst>(C);
}

template <typename Container> static size_t CountOfStack(const Container &C) {
  return CountOfType<AllocaInst>(C);
}

template <typename Container> static size_t CountOfGlobal(const Container &C) {
  return CountOfType<GlobalVariable>(C);
}

struct SizeStats {
  size_t Min = size_t(-1);
  size_t Max = 0;
  size_t Sum = 0;
  size_t N = 0;

  template <typename Container>
  static SizeStats Collect(SimpleMemoryCheck &SMC, Container &C) {
    SizeStats Stats;

    for (auto *V : C) {
      Optional<size_t> Size = SMC.getAllocSize(V);
      assert(Size);

      ++Stats.N;
      Stats.Min = std::min(Stats.Min, *Size);
      Stats.Max = std::max(Stats.Max, *Size);
      Stats.Sum += *Size;
    }

    return Stats;
  }

  void dump(llvm::raw_ostream &OS = llvm::dbgs(), bool NewLine = true) const {
    OS << "Min " << Min << ", Avg " << (N > 0 ? (Sum / N) : 0) << ", Max "
       << Max;
    if (NewLine)
      OS << "\n";
  }
};

void SimpleMemoryCheck::printStats(
    std::vector<CheckContext> &Checks,
    std::vector<Instruction *> &UninterestingMIs) {
  raw_ostream &OS = outs();
  OS << "\n=========== Start of Simple Memory Check Stats ===========\n";
  OS << "Format:\tAll instructions (Heap/Stack/Global)\n\n";

  SmallPtrSet<Value *, 32> AllAllocSites;
  SmallPtrSet<Value *, 32> AllInterestingAllocSites;
  SmallPtrSet<Value *, 32> AllOtherAllocSites;
  for (auto &Check : Checks) {
    for (auto *AS : Check.InterestingAllocSites) {
      AllAllocSites.insert(AS);
      AllInterestingAllocSites.insert(AS);
    }

    for (auto *AS : Check.OtherAllocSites) {
      AllAllocSites.insert(AS);
      AllOtherAllocSites.insert(AS);
    }
  }

  OS << "Discovered memory instructions\t" << Checks.size() << "\n";
  OS << "Discovered allocation sites\t" << AllAllocSites.size() << "\t("
     << CountOfHeap(AllAllocSites) << "/" << CountOfStack(AllAllocSites) << "/"
     << CountOfGlobal(AllAllocSites) << ")\n";
  OS << "Interesting allocation sites\t" << AllInterestingAllocSites.size()
     << "\t(" << CountOfHeap(AllInterestingAllocSites) << "/"
     << CountOfStack(AllInterestingAllocSites) << "/"
     << CountOfGlobal(AllInterestingAllocSites) << ")\n";
  OS << "Other allocation sites\t" << AllOtherAllocSites.size() << "\t("
     << CountOfHeap(AllOtherAllocSites) << "/"
     << CountOfStack(AllOtherAllocSites) << "/"
     << CountOfGlobal(AllOtherAllocSites) << ")\n";

  OS << "\n\n";
  for (size_t i = 0, e = Checks.size(); i != e; ++i) {
    const auto &C = Checks[i];
    OS << "MI " << i << (isa<LoadInst>(C.MI) ? "\tLoad" : "\tStore") << " "
       << C.AccessedBytes;

    OS << "\tSimple  " << C.InterestingAllocSites.size() << "  ("
       << CountOfHeap(C.InterestingAllocSites) << "/"
       << CountOfStack(C.InterestingAllocSites) << "/"
       << CountOfGlobal(C.InterestingAllocSites) << ")\t";

    auto Stats = SizeStats::Collect(*this, C.InterestingAllocSites);
    Stats.dump(OS, false);

    size_t DifficultGlobalCnt = 0;
    size_t DifficultStackCnt = 0;
    size_t DifficultHeapCnt = 0;
    for (auto *AS : C.OtherAllocSites) {
      if (getAllocSize(AS))
        continue;
      if (auto *GV = dyn_cast<GlobalVariable>(AS)) {
        if (!GV->hasInternalLinkage()) {
          ++DifficultGlobalCnt;
        }
      } else if (isa<AllocaInst>(AS))
        ++DifficultStackCnt;
      else if (isa<CallInst>(AS) || isa<InvokeInst>(AS))
        ++DifficultHeapCnt;
    }

    const size_t TotalDifficult =
        DifficultGlobalCnt + DifficultStackCnt + DifficultHeapCnt;
    OS << "\tDifficult  " << TotalDifficult << "  (" << DifficultHeapCnt << "/"
       << DifficultStackCnt << "/" << DifficultGlobalCnt << ")";

    OS << "\tOther  " << (C.OtherAllocSites.size() - TotalDifficult) << "  ("
       << (CountOfHeap(C.OtherAllocSites) - DifficultHeapCnt) << "/"
       << (CountOfStack(C.OtherAllocSites) - DifficultStackCnt) << "/"
       << (CountOfGlobal(C.OtherAllocSites) - DifficultGlobalCnt) << ")";

    OS << "\n";
  }

  OS << "\n===========  End of Simple Memory Check Stats  ===========\n\n";
  OS.flush();
}

char SimpleMemoryCheck::ID = 0;

static llvm::RegisterPass<SimpleMemoryCheck>
    Y("smc", "Insert array buffer checks using simple encoding");

} // end namespace seahorn
