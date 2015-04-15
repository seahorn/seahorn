/** Removes all loops */
#include "llvm/Transforms/Scalar.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Dominators.h"
using namespace llvm;

namespace 
{
  class KillLoops : public LoopPass
  {
  public:
    static char ID;
    KillLoops () : LoopPass (ID) {}
    
    bool runOnLoop (Loop *L, LPPassManager &LPM) override;

    void getAnalysisUsage(AnalysisUsage &AU) const override
    {
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.addRequired<LoopInfo>();
      AU.addRequired<ScalarEvolution>();
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

char KillLoops::ID = 0;

/// Delete all loops
bool KillLoops::runOnLoop (Loop *L, LPPassManager &LPM)
{
  BasicBlock *preheader = L->getLoopPreheader ();
  // nice pre-header in which we can terminate execution
  if (!preheader) return false;

  // single exit
  if (!L->hasDedicatedExits ()) return false;

  // -- no sub-loops
  if (L->begin () != L->end ()) return false;
  
  SmallVector<BasicBlock*, 4> exitingBlocks;
  L->getExitingBlocks(exitingBlocks);

  SmallVector<BasicBlock*, 4> exitBlocks;
  L->getUniqueExitBlocks(exitBlocks);

  bool Changed = false;
  
  ScalarEvolution &SE = getAnalysis<ScalarEvolution> ();
  SE.forgetLoop (L);
  
  // replace the terminator with unreachable instruction
  TerminatorInst *TI = preheader->getTerminator ();
  TI->eraseFromParent ();
  new UnreachableInst (preheader->getParent ()->getContext (),
                       preheader);
  
  SmallVector<PHINode *, 4> phiNodes;

  for (auto *exitBlock : exitBlocks)
  {
    BasicBlock::iterator BI = exitBlock->begin ();
    while (PHINode *P = dyn_cast<PHINode> (BI))
    {
      phiNodes.push_back (P);
      ++BI;
    }
  }
  
  for (PHINode *P : phiNodes)
    for (auto *exitingBlock : exitingBlocks)
    {
      errs () << "Removing " << *exitingBlock << " for " << *P << "\n";
      P->removeIncomingValue (exitingBlock);
      errs () << "After: " << *P << "\n";
    }
  
  
  // start removing the loop
  // based on LoopDeletion pass of LLVM
  DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  SmallVector<DomTreeNode*, 8> ChildNodes;
  for (Loop::block_iterator LI = L->block_begin(), LE = L->block_end();
       LI != LE; ++LI)
  {
    
    ChildNodes.insert(ChildNodes.begin(), DT[*LI]->begin(), DT[*LI]->end());
    for (SmallVectorImpl<DomTreeNode *>::iterator DI = ChildNodes.begin(),
           DE = ChildNodes.end(); DI != DE; ++DI) 
      DT.changeImmediateDominator(*DI, DT[preheader]);

    ChildNodes.clear();
    DT.eraseNode(*LI);
    
    (*LI)->dropAllReferences();
  }

  for (Loop::block_iterator LI = L->block_begin(), LE = L->block_end();
       LI != LE; ++LI)
    (*LI)->eraseFromParent();

  LoopInfo &loopInfo = getAnalysis<LoopInfo>();
  SmallPtrSet<BasicBlock*, 8> blocks;
  blocks.insert(L->block_begin(), L->block_end());
  for (BasicBlock *BB : blocks)
    loopInfo.removeBlock(BB);

  LPM.deleteLoopFromQueue(L);
  Changed = true;

  return Changed;
}

namespace seahorn
{
  Pass *createKillLoopsPass ()
  {return new KillLoops ();}
}


static llvm::RegisterPass<KillLoops> 
X ("kill-loops", "Deletes all loops");




