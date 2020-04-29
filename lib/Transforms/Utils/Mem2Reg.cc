//===- Mem2Reg.cpp - The -mem2reg pass, a wrapper around the Utils lib ----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass is a simple pass wrapper around the PromoteMemToReg function call
// exposed by the Utils library.
//
//===----------------------------------------------------------------------===//

// The difference with the llvm pass is that here it does not
// invalidate DSA passes.

#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/InitializePasses.h"
#include "seahorn/config.h"

using namespace llvm;

#define DEBUG_TYPE "mem2reg"

STATISTIC(NumPromoted, "Number of alloca's promoted");

namespace seahorn {

struct PromotePass : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid
  PromotePass() : FunctionPass(ID) {
    initializePromoteLegacyPassPass(*PassRegistry::getPassRegistry());
  }

  // runOnFunction - To run this pass, first we calculate the alloca
  // instructions that are safe for promotion, then we promote each one.
  //
  bool runOnFunction(Function &F) override;

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<AssumptionCacheTracker>();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.setPreservesCFG();
    // This is a cluster of orthogonal Transforms
    AU.addPreserved<UnifyFunctionExitNodes>();
    AU.addPreservedID(LowerSwitchID);
    AU.addPreservedID(LowerInvokePassID);

  }
};

char PromotePass::ID = 0;

bool PromotePass::runOnFunction(Function &F) {
  std::vector<AllocaInst *> Allocas;

  BasicBlock &BB = F.getEntryBlock(); // Get the entry node for the function

  bool Changed = false;

  DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  AssumptionCache &AC =
      getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);

  while (1) {
    Allocas.clear();

    // Find allocas that are safe to promote, by looking at all instructions in
    // the entry node
    for (BasicBlock::iterator I = BB.begin(), E = --BB.end(); I != E; ++I)
      if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) // Is it an alloca?
        if (isAllocaPromotable(AI))
          Allocas.push_back(AI);

    if (Allocas.empty())
      break;

    PromoteMemToReg(Allocas, DT, &AC);
    NumPromoted += Allocas.size();
    Changed = true;
  }

  return Changed;
}

FunctionPass *createPromoteMemoryToRegisterPass() {
  return llvm::createPromoteMemoryToRegisterPass();
}

} // end of seahorn namespace

static llvm::RegisterPass<seahorn::PromotePass> X("sea-mem2reg",
                                                  "Promote Memory to Register");
