/**
SeaHorn Verification Framework
Copyright (c) 2015 Carnegie Mellon University.
All Rights Reserved.

THIS SOFTWARE IS PROVIDED "AS IS," WITH NO WARRANTIES
WHATSOEVER. CARNEGIE MELLON UNIVERSITY EXPRESSLY DISCLAIMS TO THE
FULLEST EXTENT PERMITTEDBY LAW ALL EXPRESS, IMPLIED, AND STATUTORY
WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, AND
NON-INFRINGEMENT OF PROPRIETARY RIGHTS.

Released under a modified BSD license, please see license.txt for full
terms.

DM-0002198
*/

/// A pass to replace all variadic functions by their declarations

#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"

namespace
{
  using namespace llvm;
  class KillVarArgFn : public ModulePass
  {
  public:
    static char ID;

    KillVarArgFn () : ModulePass (ID) {}
    
    virtual bool runOnModule (Module &M) override
    {
      bool changed = false;
      for (Module::iterator FI = M.begin (), E = M.end (); FI != E; ++FI)
        if (FI->isVarArg ()) FI->deleteBody (), changed = true;
      
      return changed;
    }
    
    virtual void getAnalysisUsage (AnalysisUsage &AU) const override
    {AU.setPreservesAll ();}
    
    
  };

  char KillVarArgFn::ID = 0;
}

namespace seahorn
{
  Pass *createKillVarArgFnPass ()
  {return new KillVarArgFn ();} 
}

static llvm::RegisterPass<KillVarArgFn> X ("kill-vaarg", "Remove variadic functions");






