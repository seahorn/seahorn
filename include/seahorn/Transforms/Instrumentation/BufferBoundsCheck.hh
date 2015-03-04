#ifndef __BUFFER_BOUNDS_CHECK__HH__
#define __BUFFER_BOUNDS_CHECK__HH__

#include "seahorn/Analysis/CanAccessMemory.hh"

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/ADT/BitVector.h"
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

  public:
    static char ID;

  private:
    bool m_inline_all;

    unsigned ChecksAdded;   //! Array bounds checks added
    unsigned ChecksSkipped; //! Array bounds checks ignored because store/load is safe
    unsigned ChecksUnable;  //! Array bounds checks unable to add

  public:

    BufferBoundsCheck (bool InlineAll = false) : 
        llvm::ModulePass (ID), m_inline_all (InlineAll),
        ChecksAdded (0), ChecksSkipped (0), ChecksUnable (0) { }
    
    virtual bool runOnModule (llvm::Module &M);
    virtual bool runOnFunction (Function &F);
    
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "BufferBoundsCheck";}
    
  };
  
}

#endif
