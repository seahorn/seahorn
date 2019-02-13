#ifndef _LOWER_CONSTANT_EXPRESSIONS__HH__
#define _LOWER_CONSTANT_EXPRESSIONS__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"

#include <set>

/* Lower constant expressions to instructions */

namespace seahorn
{
  using namespace llvm;

  class LowerCstExprPass: public ModulePass 
  {
    
    bool runOnFunction(Function &F);
    ConstantExpr* hasCstExpr(Value *V, std::set<Value*> &visited);
    ConstantExpr* hasCstExpr(Value *Value);
    Instruction* lowerCstExpr(ConstantExpr * CEx, Instruction *I);
    
   public:
    
    static char ID; 
    
    LowerCstExprPass(): ModulePass (ID) {  }
    
    virtual bool runOnModule(Module &M);
    
    void getAnalysisUsage (AnalysisUsage &AU) const 
    {AU.setPreservesAll ();}

    StringRef getPassName () const override {return "LowerCstExpr";}
  };

} 

#endif 
