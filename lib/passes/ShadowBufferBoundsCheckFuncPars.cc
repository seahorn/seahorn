#include "seahorn/Transforms/ShadowBufferBoundsCheckFuncPars.hh"

#include "seahorn/Analysis/CanAccessMemory.hh"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/CallSite.h"

#include "avy/AvyDebug.h"

namespace seahorn
{
  using namespace llvm;

  char ShadowBufferBoundsCheckFuncPars::ID = 0;

  // TODO: figure out if this function is available more efficiently
  // in llvm
  Value* getArgument (Function *F, unsigned pos)
  {
    unsigned idx = 0;
    for (Function::arg_iterator I = F->arg_begin(), E = F->arg_end(); I != E;
         ++I, idx++)
    {
      if (idx == pos) return &*I; 
    }
    return NULL;
  }

  ReturnInst* getReturnInst (Function *F)
  {
    // Assume there is one single return instruction per function
    for (BasicBlock& bb : *F)
    {
      if (ReturnInst *ret = dyn_cast<ReturnInst> (bb.getTerminator ()))
        return ret;
    }
    return NULL;
  }
  
  std::pair<Value*,Value*> ShadowBufferBoundsCheckFuncPars::
  findShadowArg (Function *F, const Value *Arg) 
  {
    if (!lookup (F)) return std::pair<Value*, Value*> (NULL,NULL);
      
    size_t shadow_idx = m_orig_arg_size [F];
    Function::arg_iterator AI = F->arg_begin();
    for (size_t idx = 0 ; idx < m_orig_arg_size [F] ; ++AI, idx++)
    {
      const Value* formalPar = &*AI;
      if (formalPar == Arg)
      {
        Value* shadowOffset = getArgument (F, shadow_idx);
        Value* shadowSize   = getArgument (F, shadow_idx+1);
        assert (shadowOffset && shadowSize);
        
        return std::make_pair (shadowOffset, shadowSize);
      }
      
      if (IsShadowableType (formalPar->getType ()))
        shadow_idx += 2;
    }
    return std::pair<Value*, Value*> (NULL,NULL);
  }


  std::pair<Value*,Value*> ShadowBufferBoundsCheckFuncPars::
  findShadowRet (Function *F) 
  {
    if (IsShadowableType (F->getReturnType ()))
      return std::make_pair<Value*,Value*> (getArgument (F, F->arg_size () - 2),
                                            getArgument (F, F->arg_size () - 1));
    else
      return std::make_pair<Value*,Value*> (NULL, NULL);
  }

  bool allUsesAreCallInst (Function *F)
  { 
    for (Value::use_iterator it = F->use_begin (), et = F->use_end (); it!=et; ++it)
    {
      CallInst *CI = dyn_cast<CallInst> (*it);
      if (!CI) return false;
    }
    return true;
  }

  // For each function parameter for which we want to propagate its
  // offset and size it adds two more *undefined* function parameters
  // for placeholding its offset and size.
  bool  ShadowBufferBoundsCheckFuncPars::addFunShadowParams (Function *F, 
                                                             LLVMContext &ctx)  
  {
    if (F->getName ().startswith ("main")) return false;

    // TODO: relax this case
    if (F->hasAddressTaken ()) return false;

    // TODO: relax this case
    if (!allUsesAreCallInst (F)) return false;
    
    CanAccessMemory &CM = getAnalysis<CanAccessMemory> ();
    if (!CM.canAccess(F)) return false;

    const FunctionType *FTy = F->getFunctionType ();
    if (FTy->isVarArg ()) return false;

    // copy params
    std::vector<llvm::Type*> ParamsTy (FTy->param_begin (), FTy->param_end ());
    std::vector<Twine> NewNames;
    Function::arg_iterator FAI = F->arg_begin();
    // AttributeSet PAL = F->getAttributes ();

    for(FunctionType::param_iterator I =  FTy->param_begin (),             
            E = FTy->param_end (); I!=E; ++I, ++FAI) 
    {
      Type *PTy = *I;
      if (IsShadowableType (PTy))
      {
        ParamsTy.push_back (m_Int64Ty);
        NewNames.push_back (FAI->getName () + ".shadow.offset");
        // PAL = PAL.addAttribute(ctx, 
        //                        ParamsTy.size (), 
        //                        Attribute::ReadOnly);
        
        ParamsTy.push_back (m_Int64Ty);
        NewNames.push_back (FAI->getName () + ".shadow.size");
        // PAL = PAL.addAttribute(ctx, 
        //                        ParamsTy.size (), 
        //                        Attribute::ReadOnly);

      }
    }

    // copy return value
    Type *RetTy = F->getReturnType ();

    if (IsShadowableType (RetTy))
    {
      ReturnInst* ret = getReturnInst (F);   
      Value * retVal = ret->getReturnValue ();
      assert (retVal);
      ParamsTy.push_back (m_Int64PtrTy);
      NewNames.push_back (retVal->getName () + ".shadow.ret.offset");
      ParamsTy.push_back (m_Int64PtrTy);
      NewNames.push_back (retVal->getName () + ".shadow.ret.size");
    }

    // create function type
    FunctionType *NFTy = FunctionType::get (RetTy, 
                                            ArrayRef<llvm::Type*> (ParamsTy), 
                                            FTy->isVarArg ());

    // create new function 
    Function *NF = Function::Create (NFTy, F->getLinkage ());
    NF->copyAttributesFrom(F);
    // NF->setAttributes (PAL);
    F->getParent ()->getFunctionList ().insert(F, NF);
    NF->takeName (F);

    m_orig_arg_size [NF] = F->arg_size ();

    // new parameter names
    unsigned idx=0;
    for(Function::arg_iterator I = NF->arg_begin(), E = NF->arg_end(); 
        I != E; ++I, idx++)
    {
      if (idx >= F->arg_size ())
      {
        Value* newParam = &*I;
        newParam->setName (NewNames [idx - F->arg_size ()]);
      }
    }
    
    ValueToValueMapTy ValueMap;
    Function::arg_iterator DI = NF->arg_begin();
    for (Function::arg_iterator I = F->arg_begin(), E = F->arg_end();
         I != E; ++I, ++DI) 
    {
      DI->setName(I->getName());  // Copy the name over.
      // Add a mapping to our mapping.
      ValueMap[I] = DI;
    }
    
    SmallVector<ReturnInst*, 8> Returns; // Ignore returns.
    CloneFunctionInto (NF, F, ValueMap, false, Returns);

    IRBuilder<> B (ctx);

    // placeholders for the variables that will feed the shadow
    // variables for the return instruction of the function
    if (IsShadowableType (RetTy))
    {
      ReturnInst* ret = getReturnInst (NF);   
      B.SetInsertPoint (ret);

      Value * storeOffset =   getArgument (NF, NF->arg_size () - 2);
      Value * storeSize   =   getArgument (NF, NF->arg_size () - 1);
      B.CreateCall (m_memsafeFn, storeOffset);
      B.CreateStore (UndefValue::get (m_Int64Ty), storeOffset); 
      B.CreateCall (m_memsafeFn, storeSize);
      B.CreateStore (UndefValue::get (m_Int64Ty), storeSize); 
    }

    // Replace all callers
    while (!F->use_empty ())
    {
      // here we know all uses are call instructions
      CallSite CS (cast<Value>(F->use_back ()));

      Instruction *Call = CS.getInstruction ();
      // Copy the existing arguments
      std::vector <Value*> Args;
      Args.reserve (CS.arg_size ());
      CallSite::arg_iterator AI = CS.arg_begin ();
      for (unsigned i=0, e=FTy->getNumParams (); i!=e ; ++i, ++AI)
        Args.push_back (*AI);

      B.SetInsertPoint (Call);

      // insert placeholders for new arguments
      unsigned added_new_args = NF->arg_size () - F->arg_size();
      if (IsShadowableType (RetTy))
      {
        for(unsigned i=0; i < added_new_args - 2; i++)
          Args.push_back (UndefValue::get (m_Int64Ty)); // for shadow formal parameters
        Args.push_back  (B.CreateAlloca (m_Int64Ty));   // for shadow return offset
        Args.push_back  (B.CreateAlloca (m_Int64Ty));   // for shadow return size
      }
      else
      {
        for(unsigned i=0; i < added_new_args ; i++)
          Args.push_back (UndefValue::get (m_Int64Ty)); // for shadow formal parameters
      }

      // create new call 
      Instruction *New = B.CreateCall (NF, ArrayRef<Value*> (Args));
      cast<CallInst>(New)->setCallingConv (CS.getCallingConv ());
      cast<CallInst>(New)->setAttributes (CS.getAttributes ());
      if (cast<CallInst>(Call)->isTailCall ())
        cast<CallInst>(New)->setTailCall ();
      
      if (Call->hasName ())
        New->takeName (Call);

      // Replace all the uses of the old call
      Call->replaceAllUsesWith (New);
      
      // Remove the old call
      Call->eraseFromParent ();

      // wire up shadow actual parameters of the call with the shadow
      // formal parameters of its parent.
      CallSite NCS (const_cast<CallInst*> (cast<CallInst>(New)));

      assert (lookup (NCS.getCalledFunction ()));

      size_t  orig_arg_size = m_orig_arg_size [NCS.getCalledFunction ()];
      for (unsigned idx = 0, shadow_idx = orig_arg_size; idx < orig_arg_size; idx++)
      {
        const Value* ArgPtr = NCS.getArgument (idx);
        if (IsShadowableType (ArgPtr->getType ()))
        {
          std::pair <Value*,Value*> shadow_pars = 
              findShadowArg (New->getParent ()->getParent(), ArgPtr);
          
          if (shadow_pars.first && shadow_pars.second)
          {
            NCS.setArgument(shadow_idx,   shadow_pars.first);
            NCS.setArgument(shadow_idx+1, shadow_pars.second); 
          }

          shadow_idx +=2;
        }
      }

    }
    // Finally remove the old function
    if (!F->hasValueHandle ())
      F->eraseFromParent ();

    return true;
  } 

  bool ShadowBufferBoundsCheckFuncPars::runOnModule (llvm::Module &M)
  {
    if (m_already_done) return false;
    m_already_done = true;

    if (M.begin () == M.end ()) return false;
      
    LLVMContext &ctx = M.getContext ();

    m_Int64Ty    = Type::getInt64Ty (ctx);
    m_Int64PtrTy = m_Int64Ty->getPointerTo ();



    AttrBuilder B;
    B.addAttribute (Attribute::NoReturn);
    B.addAttribute (Attribute::ReadNone);
    
    AttributeSet as = AttributeSet::get (ctx, 
                                         AttributeSet::FunctionIndex,
                                         B);
      
    m_memsafeFn = dyn_cast<Function>
        (M.getOrInsertFunction ("verifier.memsafe",
                                as,
                                Type::getVoidTy (ctx), 
                                m_Int64PtrTy,                
                                NULL));
    
    std::vector<Function*> oldFuncs;
    for (Function &F : M) oldFuncs.push_back (&F);

    bool change = false;
    for (unsigned i=0, e = oldFuncs.size(); i!=e; ++i)
      change |= addFunShadowParams (oldFuncs [i], ctx);

    return change;
  }

    
  void ShadowBufferBoundsCheckFuncPars::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<CanAccessMemory> ();
  } 


}

static llvm::RegisterPass<seahorn::ShadowBufferBoundsCheckFuncPars> 
X ("shadow-inter-boa", 
   "Insert shadow function arguments for buffer bounds check pass");
   

