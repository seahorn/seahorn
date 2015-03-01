#ifndef __INTEGER_OVERFLOW_CHECK__HH__
#define __INTEGER_OVERFLOW_CHECK__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/ADT/BitVector.h"
#include "boost/unordered_set.hpp"


namespace seahorn
{
  using namespace llvm;
  
  class IntegerOverflowCheck : public llvm::ModulePass
  {

    Function * m_errorFn;
    BasicBlock * m_err_bb;
    BasicBlock * m_safe_bb;

    bool instrumentVal (Value *res, Type *ty,
                        IRBuilder<> B,
                        LLVMContext &ctx,
                        Instruction& inst);
    
    void instrumentErrAndSafeBlocks (IRBuilder<>B, Function &F);   


  public:

    static char ID;

  private:

    bool m_inline_all;
    unsigned ChecksAdded; 

  public:

    IntegerOverflowCheck (bool InlineAll = false) : 
        llvm::ModulePass (ID), 
        m_inline_all (InlineAll),
        ChecksAdded (0) { }
    
    virtual bool runOnModule (llvm::Module &M);
    virtual bool runOnFunction (Function &F);
    
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "IntegerOverflowCheck";}
    
  };

}

#endif
