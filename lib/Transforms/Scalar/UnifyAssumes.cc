#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
using namespace llvm;

namespace {
class UnifyAssumesPass : public ModulePass {

public:
  static char ID;
  UnifyAssumesPass() : ModulePass(ID) {}

  bool runOnModule(Module &M) override {
    Function *main = M.getFunction("main");
    if (main)
      return runOnFunction(*main);
    return false;
  }

  bool runOnFunction(Function &F);

  void processCallInst(CallInst &CI, AllocaInst &flag);

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<llvm::CallGraphWrapperPass>();
    AU.addRequired<llvm::DominatorTreeWrapperPass>();
    AU.addRequired<llvm::AssumptionCacheTracker>();
    // XXX breaks call graph
    AU.setPreservesAll();
  }

  llvm::StringRef getPassName() const override { return "UnifyAssumesPass"; }
};

char UnifyAssumesPass::ID = 0;

bool isAssumeCall(const CallInst &ci) {
  return ci.getCalledFunction() &&
         (ci.getCalledFunction()->getName().equals("verifier.assume") ||
          ci.getCalledFunction()->getName().equals("verifier.assume.not"));
}
/// Find a function exit basic block.  Assumes that the function has
/// a unique block with return instruction
llvm::BasicBlock *findExitBlock(llvm::Function &F) {
  for (llvm::BasicBlock &bb : F)
    if (llvm::isa<llvm::ReturnInst>(bb.getTerminator()))
      return &bb;
  return nullptr;
}

CallInst *findSeahornFail(llvm::Function &F) {
  for (auto &inst : instructions(F)) {
    if (auto *CI = dyn_cast<CallInst>(&inst)) {
      if (CI->getCalledFunction() &&
          CI->getCalledFunction()->getName().equals("seahorn.fail"))
        return CI;
    }
  }
  return nullptr;
}

bool UnifyAssumesPass::runOnFunction(Function &F) {
  Module &M = *F.getParent();
  Function *assumeFn = M.getFunction("verifier.assume");
  if (!assumeFn) {
    WARN << "Assumes not unified. The module has no verifier.assume()";
    assumeFn = M.getFunction("verifier.assume.not");
    if (assumeFn)
      ERR << "Unexpected definition of verifier.assume.not()";
    return false;
  }

  SmallVector<CallInst *, 16> assumes;
  for (auto &inst : instructions(F)) {
    if (auto *ci = dyn_cast<CallInst>(&inst)) {
      if (isAssumeCall(*ci))
        assumes.push_back(ci);
    }
  }
  // -- nothing to unify if there is only one assume already
  if (assumes.size() <= 1)
    return false;

  // -- make sure there is an exit block to insert the final assume
  BasicBlock *exitBlock = findExitBlock(F);
  if (!exitBlock) {
    WARN << "Assumes not unified. No return found in `main`";
    return false;
  }

  BasicBlock &entryBB = F.getEntryBlock();
  IRBuilder<> B(&entryBB, entryBB.begin());
  AllocaInst *assumeFlag;
  // -- generate code to allocate and initialize assumeFlag
  assumeFlag = B.CreateAlloca(B.getInt1Ty(), 0U, nullptr, "assume.flag");
  B.CreateStore(B.getTrue(), assumeFlag);

  // -- process all assumes
  for (auto ci : assumes)
    processCallInst(*ci, *assumeFlag);

  // -- delete all assumes
  for (auto ci : assumes)
    ci->eraseFromParent();

  // insert call to assume before the last instructions of the exit block
  // (maybe before seahorn.fail)
  CallInst* seaFailCall = findSeahornFail(F);
  if (seaFailCall) {
    B.SetInsertPoint(seaFailCall);
  } else {
    B.SetInsertPoint(exitBlock->getTerminator());
  }
  B.CreateCall(assumeFn, B.CreateLoad(assumeFlag));

  LOG("unify.dump", errs() << F << "\n";);

  // -- run mem2reg to lower assumeFlag to register
  DominatorTree &DT =
      getAnalysis<llvm::DominatorTreeWrapperPass>(F).getDomTree();
  AssumptionCache &AC =
      getAnalysis<llvm::AssumptionCacheTracker>().getAssumptionCache(F);
  PromoteMemToReg(assumeFlag, DT, &AC);

  return false;
}

void UnifyAssumesPass::processCallInst(CallInst &CI, AllocaInst &flag) {
  BasicBlock *bb = CI.getParent();
  assert(bb);

  IRBuilder<> B(bb);
  B.SetInsertPoint(&CI);

  bool isNot = CI.getCalledFunction()->getName().equals("verifier.assume.not");
  CallSite CS(&CI);

  Value *cond = CS.getArgument(0);
  if (isNot)
    cond = B.CreateNot(cond);

  // transform verifier.assume(cond) into flag := flag && cond
  B.CreateStore(B.CreateAnd(B.CreateLoad(&flag), cond), &flag);
  return;
}
} // namespace

namespace seahorn {
Pass *createUnifyAssumesPass() { return new UnifyAssumesPass(); };
} // namespace seahorn
