#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using namespace llvm;

/* This pass ensures that a block contains at most one call to
   verifier.assume

   This is useful for finding code inconsistencies. It must be run
   after all the CFG simplifications otherwise the effects of this
   pass will be undone.
*/
namespace seahorn
{
  class OneAssumePerBlock : public ModulePass
  {
   public:

    static char ID;
    Function *m_assumeFn;

    OneAssumePerBlock () : ModulePass (ID), m_assumeFn(nullptr) {}

    bool runOnModule (Module &M) {
      if (M.empty()) return false;

      if (!(M.getFunction("verifier.assume"))) return false;

      bool change = false;
      for (auto &F: M) {
        change |= runOnFunction(F);
      }
      return change;
    }

    virtual bool runOnFunction (Function &F)
    {
      if (F.empty()) return false;

      std::vector<CallInst*> workList;
      for (auto &B: F) {
        bool assumeFound = false;
        for (auto &I: B) {
          CallInst *CI = dyn_cast<CallInst> (&I);
          if (!CI) continue;
          Function* CF = CI->getCalledFunction ();
          if (!CF) continue;
          if (CF->getName ().equals ("verifier.assume")) {
            if (!assumeFound) assumeFound = true;
            else workList.push_back(CI);
          }
        }
      }

      if (workList.empty()) return false;

      while (!workList.empty())  {
        CallInst* CI = workList.back();
        workList.pop_back();
        llvm::SplitBlock(CI->getParent(), CI, this);
      }

      return true;
    }

    virtual void getAnalysisUsage (AnalysisUsage &AU) const
    {AU.setPreservesAll ();}

  };

  char OneAssumePerBlock::ID = 0;
  
  Pass *createOneAssumePerBlockPass () {return new OneAssumePerBlock ();}
  
}

