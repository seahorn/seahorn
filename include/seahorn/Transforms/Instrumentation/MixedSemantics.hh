#ifndef _MIXED_SEMANTICS_HH_
#define _MIXED_SEMANTICS_HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"

/**
 * Transforms the program into mixed semantics in which functions that
 * call error never return. Based on: 
 *
 * Arie Gurfinkel, Ou Wei, Marsha Chechik: Model Checking Recursive
 * Programs with Exact Predicate Abstraction. ATVA 2008: 95-110
 */
namespace seahorn
{
  using namespace llvm;
  
  class MixedSemantics : public ModulePass
  {
  public:
    static char ID;
    MixedSemantics () : ModulePass (ID) {}
    
    virtual bool runOnModule (Module &M) override;
    virtual void getAnalysisUsage (AnalysisUsage &AU) const override;
    virtual StringRef getPassName() const override { return "MixedSemantics"; }
  };
}

#endif /* _MIXED_SEMANTICS_HH_ */
