#ifndef DUMMY_MAIN_FUNCTION_H
#define DUMMY_MAIN_FUNCTION_H

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"

namespace seahorn
{
  using namespace llvm;
  
  class DummyMainFunction : public ModulePass
  {
    DenseMap<const Type*, Constant*> m_ndfn;

    Function& makeNewNondetFn (Module &m, Type &type, unsigned num, std::string prefix);
    Constant* getNondetFn (Type *type, Module&M);

   public:

    static char ID;
    
    DummyMainFunction () : ModulePass (ID) {}
    
    bool runOnModule (Module &M);

    void getAnalysisUsage (AnalysisUsage &AU);
    
    virtual const char* getPassName () const 
    {return "Add dummy main function";}
  };
}

#endif /* DUMMYMAINFUNCTION_H */
