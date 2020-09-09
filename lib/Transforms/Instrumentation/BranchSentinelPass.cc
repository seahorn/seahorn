/**
 * This pass adds a branch sentinel call instruction(intrinsic) before
 * every conditional branch.
 */
#include "seahorn/Analysis/SeaBuiltinsInfo.hh"
#include "seahorn/InitializePasses.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "seahorn/config.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using namespace llvm;

// TODO: add stats if useful

namespace {
struct AddBranchSentinelPass : public FunctionPass {
  static char ID;
  seahorn::SeaBuiltinsInfo *m_SBI;

  AddBranchSentinelPass() : FunctionPass(ID) {}
  void augmentBranchInstWithSentinel(BranchInst &BI, IRBuilder<> &B);
  bool runOnFunction(Function &F) override;

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<seahorn::SeaBuiltinsInfoWrapperPass>();
    // preserve nothing
  }
};
} // namespace

char AddBranchSentinelPass::ID = 0;

void AddBranchSentinelPass::augmentBranchInstWithSentinel(BranchInst &BI,
                                                          IRBuilder<> &B) {
  // inst -> basic block -> function -> module
  Module *M = BI.getParent()->getParent()->getParent();
  auto *branchSentinelFn =
      m_SBI->mkSeaBuiltinFn(seahorn::SeaBuiltinsOp::BRANCH_SENTINEL, *M);
  Value *cond = BI.getCondition();
  // create a call inst with this condition before the branch inst
  B.SetInsertPoint(&BI);
  CallInst *ci = B.CreateCall(branchSentinelFn, {cond});
  // -- a hack to locate a near-by debug location
  if (BI.getDebugLoc())
    ci->setDebugLoc(BI.getDebugLoc());
  else if (auto condInst = dyn_cast<Instruction>(BI.getCondition())) {
    ci->setDebugLoc(condInst->getDebugLoc());
  }
}

bool AddBranchSentinelPass::runOnFunction(Function &F) {
  m_SBI = &getAnalysis<seahorn::SeaBuiltinsInfoWrapperPass>().getSBI();
  IRBuilder<> builder(F.getContext());
  SmallVector<BranchInst *, 16> branches;
  for (BasicBlock &BB : F) {
    auto *TI = BB.getTerminator();
    if (BranchInst *BI = dyn_cast<BranchInst>(TI)) {
      if (BI->isConditional()) {
        branches.push_back(BI);
      } // unconditional branches are ignored
    }
  }

  for (auto *BI : branches) {
    augmentBranchInstWithSentinel(*BI, builder);
  }

  return false;
}

namespace seahorn {
FunctionPass *createAddBranchSentinelPassPass() {
  return new AddBranchSentinelPass();
}
} // namespace seahorn

using namespace seahorn;
using namespace llvm;
INITIALIZE_PASS(AddBranchSentinelPass, "branch-sentinel-pass-instrument",
                "add a branch sentinel before branch instructions", false,
                false)
