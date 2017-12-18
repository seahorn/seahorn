#include "seahorn/Transforms/Instrumentation/SimpleMemoryCheck.hh"

#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"

#include "seahorn/config.h"

#include "seahorn/Analysis/CanAccessMemory.hh"
#include "ufo/Passes/NameValues.hpp"

#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

// Seahorn dsa
#include "sea_dsa/DsaAnalysis.hh"

using namespace llvm;

namespace seahorn {

struct PtrOrigin {
  llvm::Value *Ptr;
  int64_t Offset;

  void dump() const {
    llvm::dbgs() << '<';
    if (Ptr)
      Ptr->print(dbgs());
    else
      dbgs() << "nullptr";
    dbgs() << ", " << Offset << ">\n";
  }
};

struct CheckContext {
  Instruction *MI = nullptr;
  Function *F = nullptr;
  Value *Barrier = nullptr;
  size_t AccessedBytes = 0;
  SmallVector<Value *, 8> AllocSites;

  void dump() {
    dbgs() << "CheckContext : " << (F ? F->getName() : "nullptr") << " {\n";
    dbgs() << "  MI: ";
    if (MI)
      MI->print(dbgs());
    else
      dbgs() << " nullptr";

    dbgs() << "\n  Barrier: ";
    if (Barrier)
      Barrier->print(dbgs());
    else
      dbgs() << " nullptr";

    dbgs() << "\n  AccessedBytes: " << AccessedBytes;

    dbgs() << "\n  AllocSites: {\n";
    unsigned i = 0;
    for (auto *V : AllocSites) {
      dbgs() << "    " << (i++) << ": ";
      V->print(dbgs());
      if (auto *I = dyn_cast<Instruction>(V))
        dbgs() << "  (" << I->getParent()->getName() << ")";

      dbgs() << ",\n";
    }
    dbgs() << "  }\n}\n";
  }
};

// A wrapper for seahorn dsa
class SeaDsa {
  llvm::Pass *m_abc;
  sea_dsa::DsaInfo *m_dsa;

  const sea_dsa::Cell *getCell(const llvm::Value &ptr, const llvm::Function &fn,
                               int tag) {
    assert(m_dsa);

    sea_dsa::Graph *g = m_dsa->getDsaGraph(fn);
    if (!g) {
      errs() << "WARNING ABC: Sea Dsa graph not found for " << fn.getName()
             << "\n";
      //<< " " << tag << "\n";
      return nullptr;
    }

    if (!(g->hasCell(ptr))) {
      errs() << "WARNING ABC: Sea Dsa node not found for " << ptr << "\n";
      //<< " " << tag << "\n";
      return nullptr;
    }

    const sea_dsa::Cell &c = g->getCell(ptr);
    return &c;
  }

  bool hasSuccessors(const sea_dsa::Cell &c) const {
    const sea_dsa::Node &n = *(c.getNode());
    return (std::distance(n.links().begin(), n.links().end()) > 0);
  }

public:
  SeaDsa(Pass *abc)
      : m_abc(abc),
        m_dsa(&this->m_abc->getAnalysis<sea_dsa::DsaInfoPass>().getDsaInfo()) {}

  SmallVector<Value *, 8> getAllocSites(Value *V, const Function &F) {
    auto *C = getCell(*V, F, 0);
    assert(C);
    auto *N = C->getNode();
    assert(N);

    SmallVector<Value *, 8> Sites;
    for (auto &S : N->getAllocSites())
      Sites.push_back(const_cast<Value *>(S));

    return Sites;
  };

  unsigned int getAllocSiteId(const llvm::Value &ptr) {
    return m_dsa->getAllocSiteId(&ptr);
  }

  const llvm::Value *getAllocValue(unsigned int id) {
    return m_dsa->getAllocValue(id);
  }
};

class SimpleMemoryCheck : public llvm::ModulePass {
public:
  static char ID;
  SimpleMemoryCheck() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &M);
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;
  virtual const char *getPassName() const { return "SimpleMemoryCheck"; }

private:
  LLVMContext *Ctx;
  Module *m_M;
  CallGraph *m_CG;
  const DataLayout *DL;
  const TargetLibraryInfo *TLI;
  std::unique_ptr<SeaDsa> SDSA;

  Function *m_assumeFn;
  Function *m_errorFn;
  Value *m_trackedBegin;
  Value *m_trackedEnd;
  Value *m_trackingEnbaled;

  bool isKnownAlloc(Value *Ptr);
  llvm::Optional<size_t> getAllocSize(Value *Ptr);
  PtrOrigin trackPtrOrigin(Value *Ptr);
  CheckContext getUnsafeCandidates(Instruction *Ptr, Function &F);
  bool isInterestingAllocSite(Value *Inst, int64_t LoadEnd, Value *Alloc);
  void emitGlobalInstrumentation();
  void emitMemoryInstInstrumentation(CheckContext &Candidate);
  void emitAllocSiteInstrumentation(CheckContext &Candidate, size_t AllocId);

  Function *createNewNDFn(Type *Ty, Twine Prefix = "");
  CallInst *getNDVal(size_t IntBitWidth, Function *F, IRBuilder<> &IRB,
                     Twine Name = "");
  CallInst *getNDPtr(Function *F, IRBuilder<> &IRB, Twine Name = "");
  void createAssume(Value *Cond, Function *F, IRBuilder<> &IRB);
};

llvm::ModulePass *CreateSimpleMemoryCheckPass() {
  return new SimpleMemoryCheck();
}

bool SimpleMemoryCheck::isKnownAlloc(Value *Ptr) {
  if (auto *AI = dyn_cast<AllocaInst>(Ptr)) {
    if (AI->isArrayAllocation())
      return false;

    return true;
  }

  auto *CI = dyn_cast<CallInst>(Ptr);
  if (CI && isAllocationFn(CI, TLI))
    return true;

  if (auto *GV = dyn_cast<GlobalVariable>(Ptr))
    return GV->hasInitializer();

  return false;
}

llvm::Optional<size_t> SimpleMemoryCheck::getAllocSize(Value *Ptr) {
  assert(Ptr);
  if (!isKnownAlloc(Ptr))
    return None;

  ObjectSizeOffsetEvaluator OSOE(*DL, TLI, *Ctx, true);
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
      auto *Arg = GEP->getOperand(0);

      APInt GEPOffset(DL->getPointerTypeSizeInBits(GEP->getType()), 0);
      if (!GEP->accumulateConstantOffset(*DL, GEPOffset))
        return Res;

      Res.Ptr = Arg;
      Res.Offset += GEPOffset.getSExtValue();
      continue;
    }

    return Res;
  }
}

CheckContext SimpleMemoryCheck::getUnsafeCandidates(Instruction *Inst,
                                                    Function &F) {
  assert(isa<LoadInst>(Inst) ||
         isa<StoreInst>(Inst) && "Wrong instruction type");

  Value *Arg = Inst->getOperand(isa<LoadInst>(Inst) ? 0 : 1);
  assert(Arg);

  PtrOrigin Origin = trackPtrOrigin(Arg);

  auto *Ty =
      isa<LoadInst>(Inst) ? Inst->getType() : Inst->getOperand(0)->getType();
  assert(Ty);

  const auto Bits = DL->getTypeSizeInBits(Ty);
  const uint32_t Sz = Bits < 8 ? 1 : Bits / 8;
  const int64_t LastRead = Origin.Offset + Sz;

  CheckContext Check;
  Check.MI = Inst;
  Check.F = &F;
  Check.Barrier = Origin.Ptr;
  Check.AccessedBytes = size_t(LastRead);

  Optional<size_t> AllocSize = getAllocSize(Origin.Ptr);
  if (AllocSize) {
    if (int64_t(Origin.Offset) + Sz > int64_t(*AllocSize)) {
      errs() << "Unsafe access found!\n";
      errs() << "  Allocated: " << (*AllocSize) << ", load size " << Sz
             << " at offset " << Origin.Offset << "\n";
      Check.dump();
    }

    return Check;
  }

  assert(Origin.Ptr);
  for (Value *AS : SDSA->getAllocSites(Origin.Ptr, F)) {
    if (!isInterestingAllocSite(Origin.Ptr, LastRead, AS))
      continue;

    Check.AllocSites.push_back(AS);
  }

  return Check;
}

bool SimpleMemoryCheck::isInterestingAllocSite(Value *Ptr, int64_t LoadEnd,
                                               Value *Alloc) {
  assert(Ptr);
  assert(Alloc);
  assert(LoadEnd > 0);

  Optional<size_t> AllocSize = getAllocSize(Alloc);
  if (!AllocSize)
    return false;

  return size_t(LoadEnd) > *AllocSize;
}

namespace {

Instruction *GetNextInst(Instruction *I) {
  if (I->isTerminator())
    return I;
  return I->getParent()->getInstList().getNext(I);
}

Type *CreateIntTy(const DataLayout *DL, LLVMContext &Ctx) {
  return DL->getIntPtrType(Ctx, 0);
}

Type *GetI8PtrTy(LLVMContext &Ctx) {
  return Type::getInt8Ty(Ctx)->getPointerTo();
}

Value *CreateIntCnst(Type *Ty, int64_t Val) {
  return ConstantInt::get(Ty, Val);
}

Value *CreateLoad(IRBuilder<> B, Value *Ptr, const DataLayout *DL,
                  StringRef Name = "") {
  return B.CreateAlignedLoad(Ptr, DL->getABITypeAlignment(Ptr->getType()),
                             Name);
}

static Value *CreateStore(IRBuilder<> B, Value *Val, Value *Ptr,
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
      dyn_cast<Function>(m_M->getOrInsertFunction(Name.str(), Ty, nullptr));
  assert(Res);

  if (m_CG)
    m_CG->getOrInsertFunction(Res);

  return Res;
}

CallInst *SimpleMemoryCheck::getNDVal(size_t Bits, Function *F,
                                      IRBuilder<> &IRB, Twine Name) {
  auto *Ty = IntegerType::get(*Ctx, Bits);
  auto *NondetFn = createNewNDFn(Ty, "verifier.nondet");
  CallInst *CI = IRB.CreateCall(NondetFn, None, Name);
  UpdateCallGraph(m_CG, F, CI);
  return CI;
}

CallInst *SimpleMemoryCheck::getNDPtr(Function *F, IRBuilder<> &IRB,
                                      Twine Name) {
  auto *NondetPtrFn = createNewNDFn(GetI8PtrTy(*Ctx), "verifier.nondet_ptr");
  CallInst *CI = IRB.CreateCall(NondetPtrFn, None, Name);
  UpdateCallGraph(m_CG, F, CI);
  return CI;
}

void SimpleMemoryCheck::createAssume(Value *Cond, Function *F,
                                     IRBuilder<> &IRB) {
  CallInst *CI = IRB.CreateCall(m_assumeFn, Cond);
  UpdateCallGraph(m_CG, F, CI);
}

void SimpleMemoryCheck::emitGlobalInstrumentation() {
  m_trackedBegin = CreateGlobalPtr(*m_M, "tracked_begin");
  m_trackedEnd = CreateGlobalPtr(*m_M, "tracked_end");
  m_trackingEnbaled = CreateGlobalBool(*m_M, 0, "tracking_enabled");

  Function *Main = m_M->getFunction("main");
  assert(Main);

  IRBuilder<> IRB(*Ctx);
  IRB.SetInsertPoint(&*(Main->getEntryBlock().getFirstInsertionPt()));
  CallInst *NDPtrBegin = getNDPtr(Main, IRB, "nd_ptr_begin");
  auto *Cmp1 = IRB.CreateICmpSGT(
      NDPtrBegin,
      IRB.CreateBitOrPointerCast(CreateNullptr(*Ctx), NDPtrBegin->getType()));

  createAssume(Cmp1, Main, IRB);
  CreateStore(IRB, NDPtrBegin, m_trackedBegin, DL);

  CallInst *NDPtrEnd = getNDPtr(Main, IRB, "nd_ptr_end");
  auto *Cmp2 = IRB.CreateICmpSGT(NDPtrEnd, NDPtrBegin);
  createAssume(Cmp2, Main, IRB);
  CreateStore(IRB, NDPtrEnd, m_trackedEnd, DL);

  CreateStore(IRB, ConstantInt::getFalse(*Ctx), m_trackingEnbaled, DL);
}

void SimpleMemoryCheck::emitMemoryInstInstrumentation(CheckContext &Candidate) {
  assert(isa<LoadInst>(Candidate.MI) || isa<StoreInst>(Candidate.MI));
  IRBuilder<> IRB(Candidate.MI);

  auto *BeginCandiate = IRB.CreateBitOrPointerCast(
      Candidate.Barrier, GetI8PtrTy(*Ctx), "begin_candidate");
  auto *TrackedBegin = CreateLoad(IRB, m_trackedBegin, DL, "tracked_begin");
  auto *Cmp = IRB.CreateICmpEQ(TrackedBegin, BeginCandiate);
  auto *Active = IRB.CreateLoad(m_trackingEnbaled, "active_tracking");
  auto *And = IRB.CreateAnd(Active, Cmp, "unsafe_condition");
  auto *Term = SplitBlockAndInsertIfThen(And, Candidate.MI, true);
  IRB.SetInsertPoint(Term);
  IRB.CreateCall(m_errorFn);
}

void SimpleMemoryCheck::emitAllocSiteInstrumentation(CheckContext &Candidate,
                                                     size_t AllocId) {
  assert(Candidate.AllocSites.size() > AllocId);

  Value *const Alloc = Candidate.AllocSites[AllocId];
  if (isa<GlobalVariable>(Alloc)) {
    assert(false && "Not implemented");
  }

  assert(isa<CallInst>(Alloc) || isa<AllocaInst>(Alloc));
  auto *AI = cast<Instruction>(Alloc);
  auto *CSFn = AI->getFunction();
  assert(CSFn);

  IRBuilder<> IRB(GetNextInst(AI));
  auto *Active = IRB.CreateLoad(m_trackingEnbaled, "active_tracking");
  auto *NotActive = IRB.CreateICmpEQ(Active, ConstantInt::getFalse(*Ctx),
                                     "inactive_tracking");
  auto *NDVal = getNDVal(32, CSFn, IRB);
  auto *NDBool = IRB.CreateICmpEQ(NDVal, CreateIntCnst(NDVal->getType(), 0));
  auto *TrackedEnd = CreateLoad(IRB, m_trackedEnd, DL, "loaded_end");
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
  auto *GT = IRB.CreateICmpSGT(AI, TrackedEnd);
  createAssume(GT, CSFn, IRB);

  // Start tracking.
  IRB.SetInsertPoint(ThenBB->getFirstNonPHI());
  CreateStore(IRB, ConstantInt::getTrue(*Ctx), m_trackingEnbaled, DL);
  auto *AllocI8 = IRB.CreateBitCast(AI, GetI8PtrTy(*Ctx), "alloc.i8");
  auto *TrackedBegin = CreateLoad(IRB, m_trackedBegin, DL, "loaded_begin");
  auto *AllocIsBegin =
      IRB.CreateICmpEQ(AllocI8, TrackedBegin, "alloc.is.begin");
  createAssume(AllocIsBegin, CSFn, IRB);

  Optional<size_t> AllocSize = getAllocSize(AI);
  assert(AllocSize);

  auto *End = IRB.CreateGEP(
      AllocI8,
      CreateIntCnst(IntegerType::getInt32Ty(*Ctx), int64_t(*AllocSize)),
      "end_ptr");
  auto *EndEq = IRB.CreateICmpEQ(End, TrackedEnd);
  createAssume(EndEq, CSFn, IRB);
}

bool SimpleMemoryCheck::runOnModule(llvm::Module &M) {
  if (M.begin() == M.end())
    return false;

  Function *main = M.getFunction("main");
  if (!main) {
    errs() << "Main not found: no buffer overflow checks added\n";
    return false;
  }

  Ctx = &M.getContext();
  m_M = &M;
  TLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
  DL = &M.getDataLayout();
  SDSA = llvm::make_unique<SeaDsa>(this);

  llvm::outs() << "\n\n ========== SMC  ==========\n";
  llvm::outs().flush();

  AttrBuilder AB;
  AB.addAttribute(Attribute::NoReturn);
  AttributeSet AS = AttributeSet::get(*Ctx, AttributeSet::FunctionIndex, AB);
  m_errorFn = dyn_cast<Function>(M.getOrInsertFunction(
      "verifier.error", AS, Type::getVoidTy(*Ctx), nullptr));

  AB.clear();
  AS = AttributeSet::get(*Ctx, AttributeSet::FunctionIndex, AB);
  m_assumeFn = dyn_cast<Function>(
      M.getOrInsertFunction("verifier.assume", AS, Type::getVoidTy(*Ctx),
                            Type::getInt1Ty(*Ctx), nullptr));

  IRBuilder<> B(*Ctx);
  CallGraphWrapperPass *CGWP = getAnalysisIfAvailable<CallGraphWrapperPass>();
  m_CG = CGWP ? &CGWP->getCallGraph() : nullptr;
  if (m_CG) {
    m_CG->getOrInsertFunction(m_assumeFn);
    m_CG->getOrInsertFunction(m_errorFn);
  }

  emitGlobalInstrumentation();
  M.dump();

  std::vector<CheckContext> CheckCandidates;

  for (auto &F : M) {
    // if (F.getName() != "main") continue;
    // dbgs() << "Found main\n";
    if (F.isDeclaration())
      continue;

    // Skip special functions
    if (F.getName().startswith("seahorn.") ||
        F.getName().startswith("shadow.") ||
        F.getName().startswith("verifier."))
      continue;

    // F.viewCFG();

    for (auto &BB : F) {
      for (auto &V : BB) {
        auto *I = dyn_cast<Instruction>(&V);
        if (I && (isa<LoadInst>(I) || isa<StoreInst>(I))) {

          CheckContext Check = getUnsafeCandidates(I, F);
          if (Check.AllocSites.empty())
            continue;

          CheckCandidates.emplace_back(std::move(Check));

          dbgs() << CheckCandidates.size() << ": ";
          CheckCandidates.back().dump();
        }
      }
    }
  }

  if (CheckCandidates.empty()) {
    dbgs() << "No check candidates!\n";
    return true;
  }

  size_t CheckId = 0;
  size_t AllocSiteId = 0;

  auto &Check = CheckCandidates[0];
  dbgs() << "Emitting instrumentation for check [" << CheckId << "], alloc ("
         << AllocSiteId << ")\n";
  Check.dump();

  emitMemoryInstInstrumentation(Check);
  M.dump();

  emitAllocSiteInstrumentation(Check, AllocSiteId);
  M.dump();

  errs() << " ========== SMC  ==========\n";
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

char SimpleMemoryCheck::ID = 0;

static llvm::RegisterPass<SimpleMemoryCheck>
    Y("abc-simple", "Insert array buffer checks using simple encoding");

} // end namespace seahorn
