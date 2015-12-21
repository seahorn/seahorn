#ifndef __NULL_DEREFERENCE_CHECK__HH__
#define __NULL_DEREFERENCE_CHECK__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Analysis/CallGraph.h"

namespace seahorn
{
  using namespace llvm;
  
  class NullCheck : public llvm::ModulePass {

   public:
    
    static char ID;
    
   private:
    
    unsigned  ChecksAdded; 
    unsigned  TrivialChecks; 
    Function* ErrorFn;
    // Call graph of the program
    CallGraph * CG;    

    BasicBlock* createErrorBlock (Function &F, IRBuilder<> B);
    void insertNullCheck (Value *Ptr, IRBuilder<> B, Instruction* I);

   public:
    
    NullCheck () : 
        llvm::ModulePass (ID), 
        ChecksAdded (0), TrivialChecks (0), ErrorFn (nullptr), CG (nullptr) { }
    
    virtual bool runOnModule (llvm::Module &M);
    virtual bool runOnFunction (Function &F);
    
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "NullCheck";}
    
  };
} // end namespace
#endif
