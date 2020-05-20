#include "seahorn/Analysis/SeaBuiltinsInfo.hh"
#include "seahorn/Passes.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "seahorn/Transforms/Scalar/CutLoops.hh"
#include "seahorn/InitializePasses.hh"

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"

using namespace llvm;
using namespace seahorn;

#define DEBUG_TYPE "peel-loops"

STATISTIC(LoopsPeeled, "Number of loops peeled");
STATISTIC(LoopsNotPeeled, "Number of loops cannot peel");
STATISTIC(LoopsPeelFailed, "Number of failed loop peeling attempts");

namespace {

class LoopPeelerPass : public LoopPass {
public:
  static char ID;
  // -- number of iterations to peel
  unsigned m_Num;
  LoopPeelerPass(unsigned Num = 0) : LoopPass(ID) {
    initializeLoopPeelerPassPass(*PassRegistry::getPassRegistry());
    m_Num = Num;
  }

  bool runOnLoop(Loop *L, LPPassManager &LPM) override;

  StringRef getPassName() const override { return "LoopPeeler"; }
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<seahorn::SeaBuiltinsInfoWrapperPass>();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequiredID(LoopSimplifyID);
    AU.addRequiredID(LCSSAID);

    AU.addPreserved<ScalarEvolutionWrapperPass>();
    AU.addPreserved<DominatorTreeWrapperPass>();
    // AU.addPreserved<LoopInfoWrapperPass>();
    AU.addPreservedID(LoopSimplifyID);
    AU.addPreservedID(LCSSAID);
  }
};

char LoopPeelerPass::ID = 0;
} // namespace

/**
   llvm::peeLoop() requires loops to be rotated. Here is an explanation from
   https://blog.regehr.org/archives/1603

   BEFORE Loop rotation              AFTER Loop rotation
   --------------------              --------------------

      initializer                        initializer
      goto COND                          if (condition)
    COND:                                  goto BODY
      if (condition)                     else
        goto BODY                          goto EXIT
      else                             BODY:
        goto EXIT                        body
    BODY:                                modifier
      body                               if (condition)
      modifier                             goto BODY
      goto COND                          else
    EXIT:                                  goto EXIT
                                       EXIT:

  After loop is rotated there are:
     - a pre-header in which loop condition is tested once
     - a header in which loop begins unconditionally (called BODY)
     - a unique latch with one exit branch and one backedge

  A rotated loop is easy to cut -- simply add assume(false) before the
  back-edge.

  Peeling is easy as well. Here is a comment from llvm::LoopUnrollPeel.cpp

  Peeling the first iteration transforms.

  BEFORE Peeling               AFTER Peeling
  --------------               --------------
  PreHeader:                   InsertTop:
  ...                            LoopBody
  Header:                        If (!cond) goto Exit
    LoopBody                   InsertBot:
    If (cond) goto Header      NewPreHeader:
  Exit:                        ...
                               Header:
                                LoopBody
                                If (cond) goto Header
                               Exit:
 */

bool LoopPeelerPass::runOnLoop(Loop *L, LPPassManager &LPM) {
  DOG(MSG << "Peeling loop: " << *L;);

  if (m_Num == 0) return false;

  auto *Header = L->getHeader();
  if (!Header)
    return false;
  Function *F = Header->getParent();

  auto &SEWP = getAnalysis<ScalarEvolutionWrapperPass>();
  auto *SE = &SEWP.getSE();
  auto *DTWP = getAnalysisIfAvailable<DominatorTreeWrapperPass>();
  auto *DT = DTWP ? &DTWP->getDomTree() : nullptr;
  auto *ACWP = getAnalysisIfAvailable<AssumptionCacheTracker>();
  auto *AC = ACWP ? &ACWP->getAssumptionCache(*F) : nullptr;
  auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();

  if (!canPeel(L)) {
    DOG(WARN << "Skipping loop peeling: " << *L);
    LoopsNotPeeled++;
    return false;
  }
  auto res = peelLoop(L, m_Num, &LI, SE, DT, AC, false /* PreserveLCSSA */);
  if (res)
    LoopsPeeled++;
  else
    LoopsPeelFailed++;
  return res;
}

llvm::Pass *seahorn::createLoopPeelerPass(unsigned Num) {
  return new LoopPeelerPass(Num);
}

// XXX dependencies are not listed
INITIALIZE_PASS(LoopPeelerPass, DEBUG_TYPE, "Loop Peeler", false, false);

