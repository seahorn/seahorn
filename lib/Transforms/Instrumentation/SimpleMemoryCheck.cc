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
  Value *m_trackedBegin;
  Value *m_trackedEnd;
  Value *m_trackingEnbaled;

  bool isKnownAlloc(Value *Ptr);
  llvm::Optional<size_t> getAllocSize(Value *Ptr);
  PtrOrigin trackPtrOrigin(Value *Ptr);
  CheckContext getUnsafeCandidates(Instruction *Ptr, Function &F);
  bool isInterestingAllocSite(Value *Inst, int64_t LoadEnd, Value *Alloc);
  void emitGlobalInstrumentation(Module &M);

  Function *createNewNDFn(Type *Ty, StringRef Prefix);
  CallInst *getNDVal(Function *F, IRBuilder<> &IRB);
  CallInst *getNDPtr(Function *F, IRBuilder<> &IRB);
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

static Instruction *getNextInst(Instruction *I) {
  if (I->isTerminator())
    return I;
  return I->getParent()->getInstList().getNext(I);
}

static Type *createIntTy(const DataLayout *dl, LLVMContext &ctx) {
  return dl->getIntPtrType(ctx, 0);
}

static Type *geti8PtrTy(LLVMContext &ctx) {
  return Type::getInt8Ty(ctx)->getPointerTo();
}

static Value *createIntCst(Type *ty, int64_t val) {
  return ConstantInt::get(ty, val);
}

static Value *createLoad(IRBuilder<> B, Value *Ptr, const DataLayout *dl,
                         const char *Name = "") {
  return B.CreateAlignedLoad(Ptr, dl->getABITypeAlignment(Ptr->getType()),
                             Name);
}

static Value *createStore(IRBuilder<> B, Value *Val, Value *Ptr,
                          const DataLayout *dl) {
  return B.CreateAlignedStore(Val, Ptr,
                              dl->getABITypeAlignment(Ptr->getType()));
}

static Value *createNullCst(LLVMContext &ctx) {
  return ConstantPointerNull::get(cast<PointerType>(geti8PtrTy(ctx)));
}

static Value *createGlobalBool(Module &M, unsigned val,
                               const Twine &Name = "") {
  ConstantInt *Cst = (val ? ConstantInt::getTrue(M.getContext())
                          : ConstantInt::getFalse(M.getContext()));
  GlobalVariable *GV = new GlobalVariable(M, Cst->getType(), false,
                                          GlobalValue::InternalLinkage, Cst);
  GV->setName(Name);
  return GV;
}

static Value *createGlobalPtr(Module &M, const Twine &Name = "") {
  auto NullPtr = cast<ConstantPointerNull>(createNullCst(M.getContext()));
  GlobalVariable *GV =
      new GlobalVariable(M, geti8PtrTy(M.getContext()), false, /*non-constant*/
                         GlobalValue::InternalLinkage, NullPtr);
  GV->setName(Name);
  return GV;
}

static void UpdateCallGraph(CallGraph *cg, Function *caller, CallInst *callee) {
  if (cg) {
    (*cg)[caller]->addCalledFunction(CallSite(callee),
                                     (*cg)[callee->getCalledFunction()]);
  }
}

Function *SimpleMemoryCheck::createNewNDFn(Type *Ty, StringRef Prefix) {
  auto *Res = dyn_cast<Function>(m_M->getOrInsertFunction(Prefix, Ty, nullptr));
  assert(Res);

  if (m_CG)
    m_CG->getOrInsertFunction(Res);

  return Res;
}

CallInst *SimpleMemoryCheck::getNDVal(Function *F, IRBuilder<> &IRB) {
  auto *NondetFn = createNewNDFn(geti8PtrTy(*Ctx), "verifier.nondet");
  CallInst *CI = IRB.CreateCall(NondetFn, None, "nd");
  UpdateCallGraph(m_CG, F, CI);
  return CI;
}

CallInst *SimpleMemoryCheck::getNDPtr(Function *F, IRBuilder<> &IRB) {
  auto *i8PtrTy = Type::getInt8Ty(IRB.getContext())->getPointerTo();
  auto *NondetPtrFn = createNewNDFn(i8PtrTy, "verifier.nondet_ptr");
  CallInst *CI = IRB.CreateCall(NondetPtrFn, None, "nd_ptr");
  UpdateCallGraph(m_CG, F, CI);
  return CI;
}

void SimpleMemoryCheck::createAssume(Value *Cond, Function *F,
                                     IRBuilder<> &IRB) {
  CallInst *CI = IRB.CreateCall(m_assumeFn, Cond);
  UpdateCallGraph(m_CG, F, CI);
}

void SimpleMemoryCheck::emitGlobalInstrumentation(Module &M) {
  m_trackedBegin = createGlobalPtr(M, "tracked_begin");
  m_trackedEnd = createGlobalPtr(M, "tracked_end");
  m_trackingEnbaled = createGlobalBool(M, 0, "tracking_enabled");

  Function *Main = M.getFunction("main");
  assert(Main);

  IRBuilder<> IRB(*Ctx);
  IRB.SetInsertPoint(&*(Main->getEntryBlock().getFirstInsertionPt()));
  CallInst *NDPtrBegin = getNDPtr(Main, IRB);
  auto *Cmp1 = IRB.CreateICmpSGT(
      NDPtrBegin,
      IRB.CreateBitOrPointerCast(createNullCst(*Ctx), NDPtrBegin->getType()));

  createAssume(Cmp1, Main, IRB);
  createStore(IRB, NDPtrBegin, m_trackedBegin, DL);

  CallInst *NDPtrEnd = getNDPtr(Main, IRB);
  auto *Cmp2 = IRB.CreateICmpSGT(NDPtrEnd, NDPtrBegin);
  createAssume(Cmp2, Main, IRB);
  createStore(IRB, NDPtrEnd, m_trackedEnd, DL);

  createStore(IRB, ConstantInt::getFalse(*Ctx), m_trackingEnbaled, DL);
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
  AttributeSet as = AttributeSet::get(*Ctx, AttributeSet::FunctionIndex, AB);
  Function *errorFn = dyn_cast<Function>(M.getOrInsertFunction(
      "verifier.error", as, Type::getVoidTy(*Ctx), nullptr));

  AB.clear();
  as = AttributeSet::get(*Ctx, AttributeSet::FunctionIndex, AB);
  m_assumeFn = dyn_cast<Function>(
      M.getOrInsertFunction("verifier.assume", as, Type::getVoidTy(*Ctx),
                            Type::getInt1Ty(*Ctx), nullptr));

  IRBuilder<> B(*Ctx);
  CallGraphWrapperPass *CGWP = getAnalysisIfAvailable<CallGraphWrapperPass>();
  m_CG = CGWP ? &CGWP->getCallGraph() : nullptr;
  if (m_CG) {
    m_CG->getOrInsertFunction(m_assumeFn);
    m_CG->getOrInsertFunction(errorFn);
  }

  emitGlobalInstrumentation(M);
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
