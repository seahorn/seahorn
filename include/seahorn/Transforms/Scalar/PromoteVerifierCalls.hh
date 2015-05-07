#ifndef PROMOTEVERIFIERCALLS_H
#define PROMOTEVERIFIERCALLS_H
/**
 * Promote and normalize verifier specific calls such that __VERIFIER_assume()
 */

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"

namespace seahorn
{
  using namespace llvm;
  
  struct PromoteVerifierCalls : public ModulePass
  {
    static char ID;
    
    Function *m_assumeFn;
    Function *m_assertFn;
    Function *m_errorFn;
    Function *m_failureFn;  // to indicate failure. It can only appears in main.
    
    PromoteVerifierCalls () : ModulePass (ID) {}
    
    bool runOnModule (Module &M);
    bool runOnFunction (Function &F);
    void getAnalysisUsage (AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "PromoteVerifierCalls";}
  };
}

#endif /* PROMOTEVERIFIERCALLS_H */
