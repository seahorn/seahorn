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

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils.h"

using namespace llvm;
using namespace seahorn;

#define DEBUG_TYPE "cut-loops"

namespace {
class CutLoopsPass : public LoopPass {
public:
  static char ID;
  CutLoopsPass() : LoopPass(ID) {}

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    DOG(errs() << "Cutting loop: " << *L << "\n";);

    if (!canCutLoop(L))
      return false;

    auto &SBI = getAnalysis<seahorn::SeaBuiltinsInfoWrapperPass>().getSBI();
    auto *SE = getAnalysisIfAvailable<ScalarEvolutionWrapperPass>();
    auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    return CutLoop(L, SBI, &LPM, &LI, SE ? &SE->getSE() : nullptr);
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

bool seahorn::canCutLoop(Loop *L) {
  DOG(errs() << "Checking loop to cut: " << *L << "\n";);
  BasicBlock *preheader = L->getLoopPreheader();
  if (!preheader) {
    DOG(WARN << "no-cut: no pre-header\n");
    return false;
  }
  BasicBlock *header = L->getHeader();

  if (!header) {
    DOG(WARN << "no-cut: no header\n");
    return false;
  }

  Module *M = header->getParent()->getParent();
  if (!M)
    return false;

  // single exit
  if (!L->hasDedicatedExits()) {
    DOG(WARN << "no-cut: multiple exits\n");
    return false;
  }

  // -- no sub-loops
  if (L->begin() != L->end()) {
    DOG(WARN << "no-cut: sub-loops\n");
    return false;
  }
  SmallVector<BasicBlock *, 4> latches;
  L->getLoopLatches(latches);

  for (BasicBlock *latch : latches) {
    BranchInst *bi = dyn_cast<BranchInst>(latch->getTerminator());
    if (!bi) {
      DOG(WARN << "no-cut: unsupported latch\n" << *latch << "\n";);
      return false;
    }
  }

  return true;
}

bool seahorn::CutLoop(Loop *L, seahorn::SeaBuiltinsInfo &SBI,
                      LPPassManager *LPM, LoopInfo *LI, ScalarEvolution *SE) {
  assert(canCutLoop(L));

  BasicBlock *header = L->getHeader();
  assert(header);
  Module *M = header->getParent()->getParent();
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

  if (SE)
    SE->forgetLoop(L);

  if (LI) {
    SmallPtrSet<BasicBlock *, 8> blocks;
    blocks.insert(L->block_begin(), L->block_end());

    for (BasicBlock *BB : blocks)
      LI->removeBlock(BB);

    LI->erase(L);
    LPM->markLoopAsDeleted(*L);
  }

  return true;
}

Pass *seahorn::createCutLoopsPass() { return new CutLoopsPass(); }

static llvm::RegisterPass<CutLoopsPass>
    X(DEBUG_TYPE, "Cut back-edges of all natural loops");
