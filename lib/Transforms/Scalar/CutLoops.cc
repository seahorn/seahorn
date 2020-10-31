/** Cut back-edges of all natural loops */

/**
 * Loops can be marked to be unrolled in clang using unroll pragma
 * e.g., #pragma unroll 10
 *
 * Clang does not unroll the loops itself, but marks the requested
 * unrolling depth in meta-data. The actual unrolling is done by some
 * optimization pass. For example, seaopt -O3 does the trick.
 *
 * After unrolling, CutLoops can be used to actually cut
 * back-edges. It is wired into seapp --horn-cut-loops for simplicity.
 *
 * After the loops are cut, it is helpful to optimize once more with
 * seaopt -O3
 */
#include "seahorn/Transforms/Scalar/CutLoops.hh"
#include "seahorn/Analysis/SeaBuiltinsInfo.hh"
#include "seahorn/Passes.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "seahorn/Transforms/Utils/Local.hh"

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"

using namespace llvm;
using namespace seahorn;

#define DEBUG_TYPE "cut-loops"
STATISTIC(NumLoopsCut, "Number of loops cut");
STATISTIC(NumLoopsNotCut, "Number of loops failed to cut");

namespace {
class CutLoopsPass : public FunctionPass {
public:
  static char ID;
  CutLoopsPass() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override;

  bool runOnLoop(Loop *L, LoopInfo &LI) {
    DOG(MSG << "Cutting loop: " << *L;);

    if (!canCutLoop(L))
      return false;

    Function &F = *L->getHeader()->getParent();
    auto &SBI = getAnalysis<seahorn::SeaBuiltinsInfoWrapperPass>().getSBI();
    auto *SE = getAnalysisIfAvailable<ScalarEvolutionWrapperPass>();
    auto *DTWP = getAnalysisIfAvailable<DominatorTreeWrapperPass>();
    auto *DT = DTWP ? &DTWP->getDomTree() : nullptr;
    auto *ACWP = getAnalysisIfAvailable<AssumptionCacheTracker>();
    auto *AC = ACWP ? &ACWP->getAssumptionCache(F) : nullptr;

    bool res = CutLoop(L, SBI, nullptr /* LPM */, &LI,
                       SE ? &SE->getSE() : nullptr, DT, AC);
    if (res)
      ++NumLoopsCut;
    else
      ++NumLoopsNotCut;
    return res;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<seahorn::SeaBuiltinsInfoWrapperPass>();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequiredID(LoopSimplifyID);
    AU.addRequiredID(LCSSAID);

    AU.addPreserved<ScalarEvolutionWrapperPass>();
    AU.addPreserved<DominatorTreeWrapperPass>();
    AU.addPreserved<LoopInfoWrapperPass>();
    AU.addPreservedID(LoopSimplifyID);
    AU.addPreservedID(LCSSAID);
  }
};
} // namespace

char CutLoopsPass::ID = 0;

bool CutLoopsPass::runOnFunction(Function &F) {
  auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();

  bool Changed = false;
  while (!LI.empty()) {
    Loop *L = *std::prev(LI.end());
    auto res = runOnLoop(L, LI);
    Changed |= res;
    // -- avoid infinite loops
    if (!res) {
      DOG(WARN << "Failed to cut a loop! Unexpected behaviour might occur.";);
      break;
    }
  }

  if (Changed) {
    // -- Clean up after cutting an unconditional back-edge. Such a cut creates
    // -- an unreachable basic block that has to be removed.

    // XXX This only needs to run when an unconditional back-edge was removed,
    // XXX but currently scheduling it if any change has been done at all.
    auto &SBI = getAnalysis<seahorn::SeaBuiltinsInfoWrapperPass>().getSBI();
    reduceToReturnPaths(F, SBI);
  }
  return Changed;
}

bool seahorn::canCutLoop(Loop *L) {
  DOG(MSG << "Checking loop to cut: " << *L;);
  BasicBlock *preheader = L->getLoopPreheader();
  if (!preheader) {
    DOG(WARN << "no-cut: no pre-header");
    return false;
  }
  BasicBlock *header = L->getHeader();

  if (!header) {
    DOG(WARN << "no-cut: no header");
    return false;
  }

  Module *M = header->getParent()->getParent();
  if (!M)
    return false;

  // single exit
  if (!L->hasDedicatedExits()) {
    DOG(WARN << "no-cut: multiple exits");
    return false;
  }

  // -- no sub-loops
  // if (L->begin() != L->end()) {
  //   DOG(WARN << "no-cut: sub-loops");
  //   return false;
  // }

  SmallVector<BasicBlock *, 4> latches;
  L->getLoopLatches(latches);

  for (BasicBlock *latch : latches) {
    BranchInst *bi = dyn_cast<BranchInst>(latch->getTerminator());
    if (!bi) {
      DOG(WARN << "no-cut: unsupported latch" << *latch;);
      return false;
    }
  }

  return true;
}

bool seahorn::CutLoop(Loop *L, seahorn::SeaBuiltinsInfo &SBI,
                      LPPassManager *LPM, LoopInfo *LI, ScalarEvolution *SE,
                      DominatorTree *DT, AssumptionCache *AC) {
  assert(canCutLoop(L));

  BasicBlock *header = L->getHeader();
  assert(header);
  Function *F = header->getParent();
  assert(F);
  Module *M = F->getParent();
  assert(M);
  SmallVector<BasicBlock *, 4> latches;
  L->getLoopLatches(latches);

  Function *assumeFn = SBI.mkSeaBuiltinFn(seahorn::SeaBuiltinsOp::ASSUME, *M);
  Function *assumeNotFn =
      SBI.mkSeaBuiltinFn(seahorn::SeaBuiltinsOp::ASSUME_NOT, *M);
  for (BasicBlock *latch : latches) {
    BranchInst *bi = dyn_cast<BranchInst>(latch->getTerminator());
    if (bi->isUnconditional()) {
      CallInst::Create(assumeFn, ConstantInt::getFalse(assumeFn->getContext()),
                       "", bi);
      new UnreachableInst(assumeFn->getContext(), bi);
      bi->eraseFromParent();
      // llvm::changeToUnreachable(bi, false /* UseLLVMTrap */, false /*
      // PreserveLCSSA */, nullptr, nullptr);
    } else {
      assert(bi->getSuccessor(0) == header || bi->getSuccessor(1) == header);
      // insert call to condition or not condition

      Function *fn = nullptr;
      BasicBlock *dst = nullptr;

      if (bi->getSuccessor(0) == header) {
        dst = bi->getSuccessor(1);
        fn = assumeNotFn;
      } else {
        dst = bi->getSuccessor(0);
        fn = assumeFn;
      }

      if (fn)
        CallInst::Create(fn, bi->getCondition(), "", bi);

      BranchInst::Create(dst, bi);
      bi->eraseFromParent();
    }
  }

  SmallVector<PHINode *, 8> phiNodes;
  BasicBlock::iterator BI = header->begin();
  while (PHINode *P = dyn_cast<PHINode>(BI)) {
    phiNodes.push_back(P);
    ++BI;
  }

  for (PHINode *P : phiNodes) {
    for (BasicBlock *latch : latches)
      P->removeIncomingValue(latch);
  }

  // -- update ScalarEvolution
  if (SE)
    SE->forgetLoop(L);

  // -- update LoopInfo
  if (LI) {
    auto *PL = L->getParentLoop();
    LI->erase(L);

    if (PL && LPM) {
      DOG(errs() << "Simplifying loop: " << *PL << "\n";);
      simplifyLoop(PL, DT, LI, SE, AC, nullptr /* MSSAU */,
                   false /* PreserveLCSSA */);
    }
  }

  // -- update LoopPassManager
  if (LPM)
    LPM->markLoopAsDeleted(*L);
  return true;
}

Pass *seahorn::createCutLoopsPass() { return new CutLoopsPass(); }

static llvm::RegisterPass<CutLoopsPass>
    X(DEBUG_TYPE, "Cut back-edges of all natural loops");
