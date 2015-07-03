#ifndef DUMMY_MAIN_FUNCTION_H
#define DUMMY_MAIN_FUNCTION_H

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"

namespace seahorn
{
  using namespace llvm;
  
  struct DummyMainFunction : public ModulePass
  {
    static char ID;
    std::string m_main;

    DummyMainFunction (std::string main = "") : 
      ModulePass (ID), m_main (main) {}
    
    bool runOnModule (Module &M);

    void getAnalysisUsage (AnalysisUsage &AU)
   {AU.setPreservesAll ();}
  };
}

#endif /* DUMMYMAINFUNCTION_H */
