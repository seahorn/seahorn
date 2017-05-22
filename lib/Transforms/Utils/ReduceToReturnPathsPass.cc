#include "llvm/Pass.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Transforms/Utils/Local.hh"

using namespace llvm;

namespace seahorn
{

  class ReduceToReturnPathsPass : public ModulePass
  {
   public:

    static char ID;
    
    ReduceToReturnPathsPass () : ModulePass (ID) {}

    bool runOnModule (Module &M)
    {
      for (auto&F: M) 
      { if (!F.isDeclaration ()) reduceToReturnPaths (F);}
      return true;
    }
    
    void getAnalysisUsage (AnalysisUsage &AU)
    { AU.setPreservesAll ();}
    
    virtual const char* getPassName () const 
    {return "ReduceToReturnPathsPass";}
  };


  char ReduceToReturnPathsPass::ID = 0;

  Pass* createReduceToReturnPathsPass (){
    return new ReduceToReturnPathsPass ();
  }

} // end namespace   
      
   
