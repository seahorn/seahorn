#ifndef __INTEGER_OVERFLOW_CHECK__HH__
#define __INTEGER_OVERFLOW_CHECK__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Analysis/CallGraph.h"

namespace seahorn
{
  using namespace llvm;
  
  class IntegerOverflowCheck : public llvm::ModulePass
  {

    Function * ErrorFn;
    BasicBlock * ErrorBB;
    BasicBlock * SafeBB;
    unsigned ChecksAdded; 
    CallGraph * CG; // Call graph of the program   

    bool insertIntegerCheck (Value *res, Type *ty,
                             IRBuilder<> B,
                             LLVMContext &ctx,
                             Instruction& inst);
    
    void addErrorAndSafeLocs (IRBuilder<>B, Function &F);   

    BasicBlock* createErrorBlock (Function &F, IRBuilder<> B, bool IsOverflow);

  public:

    static char ID;

    IntegerOverflowCheck () : 
        llvm::ModulePass (ID), 
        ErrorFn (nullptr), ErrorBB (nullptr), SafeBB (nullptr),
        ChecksAdded (0),
        CG (nullptr) { }
    
    virtual bool runOnModule (llvm::Module &M);
    virtual bool runOnFunction (Function &F);
    
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "IntegerOverflowCheck";}
    
  };

}

#endif
