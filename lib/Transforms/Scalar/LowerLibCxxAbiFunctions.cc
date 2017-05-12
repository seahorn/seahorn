#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/CallGraph.h"

#include "boost/range.hpp"
#include "avy/AvyDebug.h"


using namespace llvm;

namespace seahorn
{

  struct LowerLibCxxAbiFunctions : public ModulePass
  {
    static char ID;
    
    Function *m_mallocFn;
    Function *m_freeFn;
    
    LowerLibCxxAbiFunctions () : ModulePass (ID) {}
    
    bool runOnModule (Module &M)  {

      LLVMContext &Context = M.getContext ();
      AttrBuilder B;
      AttributeSet as = AttributeSet::get (Context, 
                                           AttributeSet::FunctionIndex,
                                           B);

      const DataLayout* DL = &getAnalysis<DataLayoutPass>().getDataLayout ();
      Type* IntPtrTy = DL->getIntPtrType (Context, 0);
      
      CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
      CallGraph* cg = cgwp ? &cgwp->getCallGraph () : nullptr;
      
      m_mallocFn = dyn_cast<Function>
          (M.getOrInsertFunction ("malloc", 
                                  as,
                                  Type::getInt8Ty(Context)->getPointerTo(),
                                  IntPtrTy,
                                  NULL));
      if (cg) cg->getOrInsertFunction (m_mallocFn);
    
      m_freeFn = dyn_cast<Function> 
          (M.getOrInsertFunction ("free",
                                  as,
                                  Type::getVoidTy (Context),
                                  Type::getInt8Ty(Context)->getPointerTo(),
                                  NULL));
      if (cg) cg->getOrInsertFunction (m_freeFn);
      
      for (auto &F : M) runOnFunction (F);

      return true;
    }
    
    bool runOnFunction (Function &F)  {

      CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
      CallGraph* cg = cgwp ? &cgwp->getCallGraph () : nullptr;
      
      SmallVector<Instruction*, 16> toKill;
      
      bool Changed = false;
      for (auto &I : boost::make_iterator_range (inst_begin(F), inst_end (F)))
      {
        if (!isa<CallInst> (&I)) continue;
        // -- look through pointer casts
        Value *v = I.stripPointerCasts ();
        CallSite CS (const_cast<Value*> (v));
        
        const Function *fn = CS.getCalledFunction ();
        
        // -- check if this is a call through a pointer cast
        if (!fn && CS.getCalledValue ())
          fn = dyn_cast<const Function> (CS.getCalledValue ()->stripPointerCasts ());
        
        if (fn && (fn->getName ().equals ("__cxa_allocate_exception") ||
                   fn->getName ().equals ("__cxa_allocate_dependent_exception")))
        {
          if (CS.doesNotReturn () || CS.arg_size () != 1) continue;

          IRBuilder<> Builder (F.getContext ());
          Builder.SetInsertPoint (&I);
          CallInst *ci = Builder.CreateCall (m_mallocFn, CS.getArgument(0));
          ci->setDebugLoc (I.getDebugLoc ());
          if (cg)
            (*cg)[&F]->addCalledFunction (CallSite (ci),
                                          (*cg)[ci->getCalledFunction ()]);

          LOG ("lower-libc++abi", 
               errs () << "Replaced " << I << " with " << *ci << "\n");

          I.replaceAllUsesWith (ci);
          toKill.push_back (&I);
               
        } else if (fn && (fn->getName ().equals ("__cxa_free_exception") ||
                          fn->getName ().equals ("__cxa_free_dependent_exception")))
        {
          if (!CS.doesNotReturn () || CS.arg_size () != 1) continue;

          IRBuilder<> Builder (F.getContext ());
          Builder.SetInsertPoint (&I);
          CallInst *ci = Builder.CreateCall (m_freeFn, CS.getArgument(0));
          ci->setDebugLoc (I.getDebugLoc ());

          LOG ("lower-libc++abi", 
               errs () << "Replaced " << I << " with " << *ci << "\n");

          if (cg)
            (*cg)[&F]->addCalledFunction (CallSite (ci),
                                          (*cg)[ci->getCalledFunction ()]);
          toKill.push_back (&I);
        } else if (fn && fn->getName ().equals("__cxa_throw")) {
          LOG ("lower-libc++abi", 
               errs () << "Deleted " << I << "\n");
          // Assume that after this call there is always an
          // unreachable instruction
          toKill.push_back (&I);
        }
      }
      
      for (auto *I : toKill) I->eraseFromParent ();
      
      return Changed;
    }
    
    void getAnalysisUsage (AnalysisUsage &AU) const
    {
      AU.setPreservesAll ();
      AU.addRequired<llvm::DataLayoutPass>();
      AU.addRequired<llvm::CallGraphWrapperPass>();
    }
    
    virtual const char* getPassName () const 
    {return "Lower Libc++abi functions";}

  };

  char LowerLibCxxAbiFunctions::ID = 0;

  Pass *createLowerLibCxxAbiFunctionsPass () 
  {return new  LowerLibCxxAbiFunctions();}
  
} // end namespace


