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
      AU.addRequired<LoopInfo>();
      AU.addRequiredID(LoopSimplifyID);
      AU.addRequiredID(LCSSAID);

      AU.addPreserved<ScalarEvolution>();
      AU.addPreserved<DominatorTreeWrapperPass>();
      AU.addPreserved<LoopInfo>();
      AU.addPreservedID(LoopSimplifyID);
      AU.addPreservedID(LCSSAID);
    }      
    
  };
}


char CutLoops::ID = 0;

bool CutLoops::runOnLoop (Loop *L, LPPassManager &LPM)
{
  BasicBlock *preheader = L->getLoopPreheader ();
  if (!preheader) return false;

  BasicBlock *header = L->getHeader ();
  if (!header) return false;
  
  // single exit
  if (!L->hasDedicatedExits ()) return false;

  // -- no sub-loops
  if (L->begin () != L->end ()) return false;
  
  SmallVector<BasicBlock *, 4> latches;
  L->getLoopLatches (latches);

  for (BasicBlock *latch : latches)
  {
    BranchInst *bi = dyn_cast<BranchInst> (latch->getTerminator ());
    if (!bi || bi->isUnconditional ()) return false;
  }

  for (BasicBlock *latch : latches)
  {
    BranchInst *bi = dyn_cast<BranchInst> (latch->getTerminator ());
    // insert call to condition or not condition
    assert (bi->getSuccessor (0) == header || bi->getSuccessor (1) == header);
    Function *fn = nullptr;
    BasicBlock *dst = nullptr;
    
    if (bi->getSuccessor (0) == header)
    {
      //fn = assumeNotFn;
      dst = bi->getSuccessor (1);
    }
    else 
    {
      //fn = assumeFn;
      dst = bi->getSuccessor (0);
    }

    if (fn)
      CallInst::Create (fn, bi->getCondition (),
                        "cut_loop", bi);

    
    
    BranchInst::Create (dst, bi);
    bi->eraseFromParent ();
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
  
  ScalarEvolution *SE = getAnalysisIfAvailable<ScalarEvolution> ();
  if (SE) SE->forgetLoop (L);
  
  LoopInfo &loopInfo = getAnalysis<LoopInfo>();
  SmallPtrSet<BasicBlock*, 8> blocks;
  blocks.insert(L->block_begin(), L->block_end());
  for (BasicBlock *BB : blocks)
    loopInfo.removeBlock(BB);
  
  LPM.deleteLoopFromQueue (L);
  return true;
}


namespace seahorn
{
  Pass *createCutLoopsPass ()
  {return new CutLoops ();}
}


static llvm::RegisterPass<CutLoops> 
X ("cut-loops", "Cut back-edges of all natural loops");
