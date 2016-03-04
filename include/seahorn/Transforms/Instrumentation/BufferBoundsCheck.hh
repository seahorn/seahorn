#ifndef __BUFFER_BOUNDS_CHECK__HH__
#define __BUFFER_BOUNDS_CHECK__HH__

#include "seahorn/Analysis/CanAccessMemory.hh"

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Debug.h"

#include "boost/unordered_set.hpp"

// #include "dsa/DataStructure.h"
// #include "dsa/DSGraph.h"
// #include "dsa/DSNode.h"

namespace seahorn
{
  using namespace llvm;

  class BufferBoundsCheck : public llvm::ModulePass
  {

    typedef boost::unordered_set< const Value *> ValueSet;

    const DataLayout *m_dl;
    TargetLibraryInfo *m_tli;
    //DataStructures *m_dsa;
    //ObjectSizeOffsetEvaluator *m_obj_size_eval;

    Type *m_Int64Ty;    
    Type *m_Int64PtrTy;    

    Function * m_errorFn;
    Function * m_memsafeFn;    

    BasicBlock * m_err_bb;
    BasicBlock * m_safe_bb;

    DenseMap <const Value*, Value*> m_offsets;
    DenseMap <const Value*, Value*> m_sizes;

    //uint64_t getDSNodeSize (const Value *V, DSGraph *dsg, DSGraph *gDsg);
    
    Value* lookupSize (const Value* ptr)
    {
        auto it = m_sizes.find (ptr);
        if (it != m_sizes.end ()) return it->second;
        else return nullptr;
    }

    Value* lookupOffset (const Value* ptr)
    {
        auto it = m_offsets.find (ptr);
        if (it != m_offsets.end ()) return it->second;
        else return nullptr;
    }

    void resolvePHIUsers (const Value *v, 
                          DenseMap <const Value*, Value*>& m_table);

    unsigned storageSize (const llvm::Type *t) 
    {
      return m_dl->getTypeStoreSize (const_cast<Type*> (t));
    }
    
    unsigned fieldOffset (const StructType *t, unsigned field)
    {
      return m_dl->getStructLayout (const_cast<StructType*>(t))->
          getElementOffset (field);
    }
    
    Value* createMul(IRBuilder<>B, 
                     Value *LHS, unsigned RHS, 
                     const Twine &Name = "");
    
    Value* createAdd(IRBuilder<>B, 
                     Value *LHS, Value *RHS, 
                     const Twine &Name = "");
                     
    void instrumentGepOffset(IRBuilder<> B, 
                             Instruction* insertPoint,                                    
                             const GetElementPtrInst *gep);

    void instrumentSizeAndOffsetPtr (Function* F, 
                                     IRBuilder<> B, 
                                     Instruction* insertPoint, 
                                     const Value * ptr,
                                     ValueSet &
                                     /*,DSGraph *dsg, DSGraph *gDsg*/);
    
    void instrumentSizeAndOffsetPtr (Function* F,
                                     IRBuilder<> B, 
                                     Instruction* insertPoint, 
                                     const Value * ptr
                                     /*,DSGraph *dsg, DSGraph *gDsg*/);
    
    bool instrumentCheck (IRBuilder<> B, 
                          Instruction& insertPoint, 
                          const Value& ptr);
    
    bool instrumentCheck (IRBuilder<> B, 
                          Instruction& inst, 
                          const Value& ptr,
                          const Value& len);
    
    void instrumentErrAndSafeBlocks (IRBuilder<>B, Function &F);   

    /************************************/
    /*   To shadow function parameters  */
    /************************************/

    DenseMap <const Function *, size_t > m_orig_arg_size;
    // keep track of the store instructions for returning by ref the
    // shadow offset and size parameters.
    DenseMap <const Function*,  
              std::pair<StoreInst*,StoreInst* > > m_ret_shadows;

    bool addFunShadowParams (Function *F, LLVMContext &ctx);  

    bool lookup (const Function *F) const
    {
      auto it = m_orig_arg_size.find (F);
      return (it != m_orig_arg_size.end ());
    }

    bool IsShadowableFunction (const Function &F) const  
    { 
      auto it = m_orig_arg_size.find (&F);
      if (it == m_orig_arg_size.end ()) return false;
      return (F.arg_size () > it->second);
      //return (m_orig_arg_size.find (&F) != m_orig_arg_size.end ());
    }

    bool IsShadowableType (Type * ty) const { return ty->isPointerTy (); } 
    
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

    std::pair<StoreInst*, StoreInst*> findShadowRet (Function *F) {
      return m_ret_shadows [F];
    }

  public:
    static char ID;

  private:

    unsigned ChecksAdded;   //! Array bounds checks added
    unsigned ChecksSkipped; //! Array bounds checks ignored because store/load is safe
    unsigned ChecksUnable;  //! Array bounds checks unable to add

  public:

    BufferBoundsCheck () : llvm::ModulePass (ID), 
                           ChecksAdded (0), 
                           ChecksSkipped (0), 
                           ChecksUnable (0) { }
    
    virtual bool runOnModule (llvm::Module &M);
    virtual bool runOnFunction (Function &F);
    
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "BufferBoundsCheck";}
    
  };
  
}

#endif
