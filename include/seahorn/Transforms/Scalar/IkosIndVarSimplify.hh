#ifndef IKOSINDVARSIMPLIFY 
#define IKOSINDVARSIMPLIFY 

#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolutionExpander.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Target/TargetLibraryInfo.h"

using namespace llvm;

namespace seahorn {

  class IkosIndVarSimplify : public LoopPass 
  {
    LoopInfo        *LI;
    ScalarEvolution *SE;
    DominatorTree   *DT;
    const DataLayout      *TD;
    TargetLibraryInfo *TLI;

    SmallVector<WeakVH, 16> DeadInsts;
    bool Changed;

  public:

    static char ID; 

    IkosIndVarSimplify() : 
        LoopPass(ID), LI(0), SE(0), DT(0), TD(0), Changed(false) 
    { }

    virtual bool runOnLoop(Loop *L, LPPassManager &LPM);

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.addRequired<LoopInfo>();
      AU.addRequired<ScalarEvolution>();
      //AU.addRequiredID(LoopSimplifyID);
      //AU.addRequiredID(LCSSAID);
      AU.addPreserved<ScalarEvolution>();
      //AU.addPreservedID(LoopSimplifyID);
      //AU.addPreservedID(LCSSAID);
      AU.setPreservesCFG();
    }

    virtual const char* getPassName () const {return "IkosIndVarSimplify";}

  private:

    virtual void releaseMemory() { DeadInsts.clear(); }

    bool isValidRewrite(Value *FromVal, Value *ToVal);

    void HandleFloatingPointIV(Loop *L, PHINode *PH);
    void RewriteNonIntegerIVs(Loop *L);

    void SimplifyAndExtend(Loop *L, SCEVExpander &Rewriter, LPPassManager &LPM);

    void RewriteLoopExitValues(Loop *L, SCEVExpander &Rewriter);

    Value *LinearFunctionTestReplace(Loop *L, const SCEV *BackedgeTakenCount,
                                     PHINode *IndVar, SCEVExpander &Rewriter);

    void SinkUnusedInvariants(Loop *L);
  };

} // end namespace

#endif 
