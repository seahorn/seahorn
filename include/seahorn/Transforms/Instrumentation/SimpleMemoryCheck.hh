#ifndef SIMPLE_MEMORY_CHECK__HH
#define SIMPLE_MEMORY_CHECK__HH

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Debug.h"

#include "seahorn/config.h"

namespace seahorn
{

  class SimpleMemoryCheck : public llvm::ModulePass
  {
   public:

    static char ID;
    SimpleMemoryCheck (): llvm::ModulePass (ID) { }
    virtual bool runOnModule (llvm::Module &M);
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const
    {return "SimpleMemoryCheck";}
    
  };

}

#endif
