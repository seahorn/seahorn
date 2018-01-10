#ifndef __NAME_VALUES__HPP_
#define __NAME_VALUES__HPP_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"


namespace ufo
{
  using namespace llvm;

  struct NameValues : public ModulePass
  {
    static char ID;
    NameValues () : ModulePass (ID) {}
    bool runOnModule (Module &M);
    bool runOnFunction (Function &F);
    void getAnalysisUsage (AnalysisUsage &AU) const { AU.setPreservesAll (); }
    virtual const char* getPassName () const {return "NameValues";}

  };

    inline Pass *createNameValuesPass(){return new NameValues();}
}

#endif
