#ifndef SHADOW_BUFFER_BOUNDS_CHECK_FUNC_PARAMS_H
#define SHADOW_BUFFER_BOUNDS_CHECK_FUNC_PARAMS_H

/**
 * Add two shadow parameters (offset and size) for each function
 * parameter and return value for which the Buffer Bounds Check pass
 * will keep track of its offset and size.
 *
 * All the shadow parameters for function parameters are inputs while
 * those for return values are output.
 */

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Debug.h"

namespace seahorn
{
  using namespace llvm;
  
  class ShadowBufferBoundsCheckFuncPars : public ModulePass
  {


    DenseMap <const Function *, size_t > m_orig_arg_size;

    Type *m_Int64Ty;    
    Type *m_Int64PtrTy;    

    Function * m_memsafeFn;    

    bool addFunShadowParams (Function *F, LLVMContext &ctx);  

    bool m_already_done;

    bool lookup (const Function *F) const
    {
      auto it = m_orig_arg_size.find (F);
      return (it != m_orig_arg_size.end ());
    }

   public:

    static char ID;
    
    ShadowBufferBoundsCheckFuncPars () : ModulePass (ID), m_already_done (false) {}
    
    bool runOnModule (Module &M);

    void getAnalysisUsage (AnalysisUsage &AU) const;

    bool IsShadowableFunction (const Function &F) const  
    { 
      auto it = m_orig_arg_size.find (&F);
      if (it == m_orig_arg_size.end ()) return false;
      return (F.arg_size () > it->second);
      
      //return (m_orig_arg_size.find (&F) != m_orig_arg_size.end ());
    }

    bool IsShadowableType (Type * ty) const
    {
      return ty->isPointerTy ();
    }
    
    // return the number of original arguments before the pass added
    // shadow parameters
    size_t getOrigArgSize (const Function &F) 
    {
      assert (IsShadowableFunction (F));
      return m_orig_arg_size [&F];
    }
    
    // Formal parameters of F are x1 x2 ... xn y1 ... ym where x1...xn
    // are the original formal parameters and y1...ym are the shadow
    // parameters to propagate offset and size. y1...ym is a sequence
    // of offset,size,...,offset,size. 
    //
    // This function returns the pair of shadow variables
    // <offset,size> corresponding to Arg if there exists, otherwise
    // returns a pair of null pointers.
    std::pair<Value*,Value*> findShadowArg (Function *F, const Value *Arg);

    // This function returns the pair of shadow variables
    // <offset,size> corresponding to the return value of the function
    // if there exists, otherwise returns a pair of null pointers.
    std::pair<Value*,Value*> findShadowRet (Function *F);

    // Resolve the variables that feed the shadow variables for the
    // return value of the function.
    bool resolveShadowRetDefs (Function *F, Value* Offset, Value* Size)
    {
      auto p = findShadowRet (F);
      Value *ShadowOff  = p.first;
      Value *ShadowSize = p.second;

      if (!(ShadowOff && ShadowSize)) return false; 
      
      assert (ShadowOff->hasOneUse ());
      assert (ShadowSize->hasOneUse ());
      (*ShadowOff->user_begin  ())->setOperand(0, Offset);
      (*ShadowSize->user_begin ())->setOperand(0, Size);
      return true;
    }
     
    virtual const char* getPassName () const {return "ShadowBufferBoundsCheckFuncPars";}
  };
}

#endif 
