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
#include "llvm/Transforms/Scalar.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Module.h"

#include "seahorn/Support/SeaDebug.h"
using namespace llvm;

namespace 
{
  class CutLoops : public LoopPass
  {
  public:
    static char ID;
    CutLoops () : LoopPass (ID) {}

    bool runOnLoop (Loop *L, LPPassManager &LPM) override;
    void getAnalysisUsage(AnalysisUsage &AU) const override 
    {
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
}


char CutLoops::ID = 0;

bool CutLoops::runOnLoop (Loop *L, LPPassManager &LPM)
{
  LOG("cut-loops", errs () << "Cutting loop: " << *L << "\n";);
  
  BasicBlock *preheader = L->getLoopPreheader ();
  if (!preheader)
  {
    LOG("cut-loops", errs () << "Warning: no-cut: no pre-header\n");
    return false;
  }
  

  BasicBlock *header = L->getHeader ();

  if (!header)
  {
    LOG("cut-loops", errs () << "Warning: no-cut: no header\n");
    return false;
  }
  
  Module *M = header->getParent ()->getParent ();
  if (!M) return false;
  
  // single exit
  if (!L->hasDedicatedExits ())
  {
    LOG("cut-loops", errs () << "Warning: no-cut: multiple exits\n");
    return false;
  }
  

  // -- no sub-loops
  if (L->begin () != L->end ())
  {
    LOG("cut-loops", errs () << "Warning: no-cut: sub-loops\n");
    return false;
  }
  
  
  SmallVector<BasicBlock *, 4> latches;
  L->getLoopLatches (latches);

  for (BasicBlock *latch : latches)
  {
    BranchInst *bi = dyn_cast<BranchInst> (latch->getTerminator ());
    if (!bi)
    {
      LOG("cut-loops", errs () << "Warning: no-cut: unsupported latch\n"
          << *latch << "\n";);
      return false;
    }
    
  }

  
  Function *assumeFn = M->getFunction ("verifier.assume");
  if (!assumeFn)
  {
    LOG ("cut-loops", errs () << "Missing verifier.assume()\n";);
    return false;
  }
  
  Function *assumeNotFn = M->getFunction ("verifier.assume.not");
  if (!assumeNotFn)
  {
    LOG ("cut-loops", errs () << "Missing verifier.assume.not()\n";);
    return false;
  }
  
  
  for (BasicBlock *latch : latches)
  {
    BranchInst *bi = dyn_cast<BranchInst> (latch->getTerminator ());
    if (bi->isUnconditional ())
    {
      CallInst::Create (assumeFn,
                        ConstantInt::getFalse (assumeFn->getContext ()), "", bi);
      new UnreachableInst (assumeFn->getContext (), bi);
      bi->eraseFromParent ();
    }
    else
    {
      assert (bi->getSuccessor (0) == header || bi->getSuccessor (1) == header);
      // insert call to condition or not condition
    
      Function *fn = nullptr;
      BasicBlock *dst = nullptr;
    
      if (bi->getSuccessor (0) == header)
      {
        dst = bi->getSuccessor (1);
        fn = assumeNotFn;
      }
      else 
      {
        dst = bi->getSuccessor (0);
        fn = assumeFn;
      }

      if (fn)
        CallInst::Create (fn, bi->getCondition (),
                          "", bi);

      BranchInst::Create (dst, bi);
      bi->eraseFromParent ();
    }
  }
  
  SmallVector<PHINode*, 8> phiNodes;
  BasicBlock::iterator BI = header->begin ();
  while (PHINode *P = dyn_cast<PHINode> (BI))
  {
    phiNodes.push_back (P);
    ++BI;
  }

  for (PHINode *P : phiNodes)
    for (BasicBlock *latch : latches)
      P->removeIncomingValue (latch);

  if (ScalarEvolutionWrapperPass *SEWP = getAnalysisIfAvailable<ScalarEvolutionWrapperPass> ()) {
    ScalarEvolution &SE = SEWP->getSE();
    SE.forgetLoop (L);
  }
  
  LoopInfo &loopInfo = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
  SmallPtrSet<BasicBlock*, 8> blocks;
  blocks.insert(L->block_begin(), L->block_end());
  for (BasicBlock *BB : blocks)
    loopInfo.removeBlock(BB);

  // llvm 3.8
  loopInfo.markAsRemoved(L);
  // llvm 3.6
  //LPM.deleteLoopFromQueue (L);
  return true;
}


namespace seahorn
{
  Pass *createCutLoopsPass ()
  {return new CutLoops ();}
}


static llvm::RegisterPass<CutLoops> 
X ("cut-loops", "Cut back-edges of all natural loops");
