/** Insert dummy exit basic blocks */
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"

using namespace llvm;

namespace seahorn
{
  class DummyExitBlock : public FunctionPass
  {
  public:
    static char ID;
    DummyExitBlock () : FunctionPass (ID) {}

    virtual void getAnalysisUsage (AnalysisUsage &AU) const override
    {AU.setPreservesAll ();}

    virtual bool runOnFunction (Function &F) override
    {
      // -- see if there is a return instruction already
      for (const BasicBlock &bb : F)
        if (isa<ReturnInst> (bb.getTerminator ())) return false;
      
      BasicBlock *NewRetBlock = BasicBlock::Create (F.getContext (),
                                                    "DummyExitBlock", &F);
      if (F.getReturnType ()->isVoidTy ())
        ReturnInst::Create (F.getContext (), NULL, NewRetBlock);
      else 
        ReturnInst::Create (F.getContext (),
                            Constant::getNullValue (F.getReturnType ()),
                            NewRetBlock);
      return true;
    }
  };

  char DummyExitBlock::ID = 0;
  
  Pass *createDummyExitBlockPass () {return new DummyExitBlock ();}
  
}

