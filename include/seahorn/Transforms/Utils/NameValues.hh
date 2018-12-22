#pragma once

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"


namespace seahorn
{
  using namespace llvm;

  struct NameValues : public ModulePass
  {
    static char ID;
    NameValues () : ModulePass (ID) {}
    bool runOnModule (Module &M);
    bool runOnFunction (Function &F);
    void getAnalysisUsage (AnalysisUsage &AU) const { AU.setPreservesAll (); }
    StringRef getPassName() const override { return "NameValues"; }
  };

    inline Pass *createNameValuesPass(){return new NameValues();}
}

