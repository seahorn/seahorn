#ifndef __ARRAY_BOUNDS_CHECK__HH__
#define __ARRAY_BOUNDS_CHECK__HH__

/*
  Encodings to instrument a program for Array Bounds Check (ABC).

  - Local encodes each pointer separately by adding two ghost
    variables which correspond to the offset and size of the
    pointer. This encoding is simplest one. 

    Note that another local encoding would be to add as well two ghost
    variables but this time the min and max offset per pointer. This
    is not implemented.

  - Global encodes all pointers by keeping track of a global offset
    and size that switch non-deterministically from pointer to
    pointer. The instrumentation is much simpler since we only have
    very few global variables. More importantly, the encoding tries to
    group pointers that share a similar proof (e.g., correspond to the
    same allocation site).

  - GlobalCCallbacks: unlike Local and Global, GlobalCCallbacks
    only inserts special functions which are then defined at the
    C-level. This is very useful to prototype different variants.
 */ 

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Debug.h"

#include "seahorn/config.h"

#include "boost/unordered_set.hpp"

namespace seahorn
{
   using namespace llvm;
   class DsaWrapper;

  /* 
     Local encoding.

     For each pointer dereference *p we add two shadow registers:
     p.offset and p.size. p.offset is the distance from the base address
     of the object that contains p to actual p and p.size is the actual
     size of the allocated memory for p (including padding). Note that
     for stack and static allocations p.size is always know but for
     malloc-like allocations p.size may be unknown.

     Then, for each pointer dereference *p we add two assertions:
       [underflow]  assert (p.offset >= 0)
       [overflow ]  assert (p.offset + p.addr_size <= p.size)
       where p.addr_size is statically known by llvm.

     For instrumenting a function f we add for each dereferenceable
     formal parameter x two more shadow formal parameters x.offset and
     x.size. Then, at a call site of f and for a dereferenceable actual
     parameter y we add its corresponding y.offset and y.size. To
     instrument the return value of a function we just keep of two
     shadow global variables ret.offset and ret.size so that the callee
     updates them before it returns to the caller.

     If the instrumented program does not violate any of the assertions
     then the original program is free of buffer overflows/underflows.

     TODO: 
       - instrument pointers originated from loads.
       - instrument intToPtr instructions
  */
  class Local : public llvm::ModulePass
  {
    typedef boost::unordered_set< const Value *> ValueSet;

    const DataLayout *m_dl;
    TargetLibraryInfo *m_tli;

    Type *m_IntPtrTy;    

    Function * m_errorFn;

    Value* m_ret_offset;
    Value* m_ret_size;

    unsigned m_mem_accesses;   //! total number of instrumented mem accesses
    unsigned m_checks_added;   //! checks added
    unsigned m_trivial_checks; //! checks ignored because they are safe
    unsigned m_checks_unable;  //! checks unable to add

    DenseMap <const Value*, Value*> m_offsets;
    DenseMap <const Value*, Value*> m_sizes;

    Value* lookupSize (const Value* ptr);
    Value* lookupOffset (const Value* ptr);

    /* To instrument accesses */

    void resolvePHIUsers (const Value *v, 
                          DenseMap <const Value*, Value*>& m_table);
                     
    void instrumentGepOffset(IRBuilder<> B, Instruction* insertPoint,
                             const GetElementPtrInst *gep);

    void instrumentSizeAndOffsetPtrRec (Function* F, IRBuilder<> B, 
                                        Instruction* insertPoint, 
                                        const Value * ptr, ValueSet & visited);
    
    void instrumentSizeAndOffsetPtr (Function* F, IRBuilder<> B, 
                                     Instruction* insertPoint, const Value * ptr);
      
    bool instrumentCheck (Function& F, IRBuilder<> B, Instruction& inst, 
                          const Value& ptr, Value* len);
    
    /*   To shadow function parameters  */

    DenseMap <const Function *, size_t > m_orig_arg_size;
    // keep track of the store instructions for returning the shadow
    // offset and size return parameters.
    typedef std::pair<StoreInst*,StoreInst* > StoreInstPair;
    typedef std::pair<Value*,Value*> ValuePair;
    DenseMap <const Function*,  StoreInstPair> m_ret_shadows;

    bool addFunShadowParams (Function *F, LLVMContext &ctx);  

    bool IsShadowableFunction (const Function &F) const;  
    bool IsShadowableType (Type * ty) const;
    // return the number of original arguments before adding shadow
    // parameters
    size_t getOrigArgSize (const Function &F) ;
    
    // Formal parameters of F are x1 x2 ... xn y1 ... ym where x1...xn
    // are the original formal parameters and y1...ym are the shadow
    // parameters to propagate offset and size. y1...ym is a sequence
    // of offset,size,...,offset,size. 
    //
    // This function returns the pair of shadow variables
    // <offset,size> corresponding to Arg if there exists, otherwise
    // returns a pair of null pointers.
    ValuePair findShadowArg (Function *F, const Value *Arg);
    StoreInstPair findShadowRet (Function *F);

  public:

    static char ID;

    Local () : llvm::ModulePass (ID), 
              m_dl (nullptr), m_tli (nullptr),
              m_IntPtrTy (nullptr), 
              m_errorFn (nullptr), 
              m_mem_accesses (0), m_checks_added (0), 
              m_trivial_checks (0), m_checks_unable (0) { }
    
    virtual bool runOnModule (llvm::Module &M);
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const
    {return "ArrayBoundsCheck using Local encoding";}
  };

  /* 
     Global encoding.

     The encoding keeps track only of four global variables: 

     - g_base (pointer), 
     - g_ptr (pointer), 
     - g_size (integer), and
     - g_offset (integer) 

     where g_ptr is some address between [g_base,..., g_base + g_size - addr_size] 
     and g_offset is g_ptr - g_base

     Initially:
        assume (g_base > 0);
        g_ptr = null;
        assume (g_size > 0);
        g_offset = 0;
   
     For each allocation site p := alloc (n):
        if (!g_ptr && p == g_base) {
          g_ptr = g_base;
          g_size = n;
          g_offset = 0;
        }
        else {
         assume (g_base + g_size < p);
        }
    
     For each p := q + n:
        if (nd () && g_ptr && q == g_base) {
          g_ptr = p;
          g_offset = n;
        }

     For each memory access *p := rhs or lhs := *p:
        if (g_ptr && p == g_ptr) {
          assert (g_offset + p.addr_size <= g_size);
          assert (g_offset >= 0);
        }
  */
  class Global : public llvm::ModulePass
  {
    class InstVis {
      
      const DataLayout*  m_dl;
      const TargetLibraryInfo* m_tli;
      IRBuilder<> m_B;
      CallGraph  *m_cg;
      DsaWrapper *m_dsa;
      ObjectSizeOffsetEvaluator m_eval;
      Type *m_IntPtrTy;    
      unsigned m_nondet_id;
      
      /// tracked_ptr is some aligned address between 
      ///    [tracked_base, ... , tracked_base + tracked_size - address_sizeof(tracked_ptr))]
      /// m_tracked_offset = m_tracked_ptr - m_tracked_base
      Value* m_tracked_base; 
      Value* m_tracked_ptr;
      Value* m_tracked_offset;
      Value* m_tracked_size;
      Value* m_tracked_escaped_ptr;

      Function* m_errorFn;
      Function* m_assumeFn;

     public: // counters for stats

      
      unsigned m_checks_added;   
      unsigned m_trivial_checks;
      unsigned m_untracked_dsa_checks;
      unsigned m_mem_accesses;

      unsigned m_intrinsics_checks_added;
      unsigned m_gep_known_size_and_offset_checks_added;
      unsigned m_gep_known_size_checks_added;
      unsigned m_gep_unknown_size_checks_added;
      unsigned m_non_gep_known_size_checks_added;
      unsigned m_non_gep_unknown_size_checks_added;

      /* helpers */
      
      BasicBlock* Assert (Value* cond, BasicBlock* then, BasicBlock* cur, 
                          Instruction* inst, const Twine &errorBBName);

      void Assume (Value* cond, Function* F);

      Function& createNewNondetFn (Module &m, Type &type, unsigned num, std::string prefix);
      
      CallInst* NonDet (Function* caller);

      CallInst* NonDetPtr (Function* caller);

      bool globalGeneratedBySeaHorn (Value* V) {
        return (V == m_tracked_base || V == m_tracked_ptr ||
                V == m_tracked_offset || V == m_tracked_size || 
                V == m_tracked_escaped_ptr);
      }
        
      std::string mkBBName (const Twine& Prefix, Value* V) {
        if (V && V->hasName ()) {
          Twine name = Prefix + "_" + V->getName () + "_bb";
          return name.str();
        }
        else  { 
          Twine name = Prefix + "_bb"; 
          return name.str ();
        }
      }
      
     /*main operations*/

      //! Initialization of base, offset, and size.
      void doInit (Module& M);

      //! Instrument any allocation site
      void doAllocaSite (Value* ptr, Value* size, Instruction* insertPt);
   
      //! Instrument pointer arithmetic
      void doPtrArith (GetElementPtrInst * gep, Instruction* insertPt);
            
      //! Instrument any read or write to a pointer
      void doGepOffsetCheck (GetElementPtrInst* gep, uint64_t size, Instruction* insertPt);
      void doGepPtrCheck (GetElementPtrInst* gep, Instruction* insertPt);
      void doPtrCheck (Value* ptr, Value* n, Instruction* insertPt);

     public:
      
      InstVis (Module& M, 
	       const DataLayout* dl, const TargetLibraryInfo* tli,
	       IRBuilder<> B, CallGraph* cg, DsaWrapper * dsa,
	       Function* errorFn, Function* assumeFn);
      
      void visit (GetElementPtrInst *I);
      void visit (LoadInst *I);
      void visit (StoreInst *I);
      void visit (MemTransferInst *MTI);
      void visit (MemSetInst *MSI);
      void visit (AllocaInst *I);
      void visit (IntToPtrInst *I);
      void visit (InsertValueInst *I);
      void visit (ExtractValueInst *I);            
      void visit (CallInst *I);
      void visit (Function *F);
      
    }; // end class
    
   public:

    static char ID;
    Global (): llvm::ModulePass (ID) { }
    virtual bool runOnModule (llvm::Module &M);
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const
    {return "ArrayBoundsCheck using Global encoding";}
    
  };


  /* 
     Third encoding.

     Assume that the analyzed program includes some predefined functions:

     - void sea_abc_init(void);
     - void sea_abc_alloc (uint64_t *base, uint64_t size);
     - void sea_abc_log_ptr (uint8_t *base, uint64_t offset);
     - void sea_abc_log_load_ptr (uint8_t *base);
     - void sea_abc_log_store_ptr (uint8_t *base);
     - void sea_abc_assert_valid_ptr (uint8_t *base, uint64_t offset);
     - void sea_abc_assert_valid_offset (uint64_t offset, uint64_t size);

     This encoding simply calls to these functions.
  */
  class GlobalCCallbacks : public llvm::ModulePass
  {

   public:
    static char ID;
    GlobalCCallbacks ():  llvm::ModulePass (ID) { }
    virtual bool runOnModule (llvm::Module &M);
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const
    {return "ArrayBoundsCheck using Global encoding by calling C-defined functions";}
  };

}

#endif
