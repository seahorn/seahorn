#ifndef _LOWER_GV_INITIALIZERS__HH__
#define _LOWER_GV_INITIALIZERS__HH__

/** Pass to lower scalar initializers to global variables into
    explicit initialization code */

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/DataLayout.h"

namespace seahorn
{
  using namespace llvm;
  
  class LowerGvInitializers : public ModulePass
  {

    DenseMap<const Type*, FunctionCallee> m_ndfn;

    FunctionCallee getNondetFn (Type *type, Module& M);
      
  public:
    
    static char ID;
    
    LowerGvInitializers () : ModulePass (ID) {}
    
    virtual bool runOnModule (Module &M) override;

    void getAnalysisUsage (AnalysisUsage &AU) const  override {
      AU.setPreservesAll ();
    }
    
  };
}




#endif /* _LOWER_GV_INITIALIZERS__HH__ */
