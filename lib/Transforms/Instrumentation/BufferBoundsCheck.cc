/* 
   Instrument a program to add buffer overflow/ underflow checks.

   For each pointer dereference *p we add two shadow registers:
   p.offset and p.size. p.offset is the offset from the base address
   of the object that contains p and p.size is the actual size of the
   allocated memory for p (including padding). Note that for stack and
   static allocations p.size is always know but for malloc-like
   allocations p.size may be unknown.

   Then, for each pointer dereference *p we add two assertions:
     [underflow]  assert (p.offset >= 0)
     [overflow ]  assert (p.offset < p.size)

   For instrumenting a function f we add for each dereferenceable
   formal parameter x two more shadow formal parameters x.offset and
   x.size. Then, at a call site of f and for a dereferenceable actual
   parameter y we add its corresponding y.offset and y.size. Moreover,
   for each function that returns a pointer we add two more shadow
   formal parameters to represent the size and offset of the returned
   value. The difference here is that these two shadow variables must
   be passed by reference at the call site so the continuation can use
   those. Thus, rather than using registers we allocate them in the
   stack and pass their addresses to the callee.

   If the instrumented program does not violate any of the assertions
   then the original program is free of buffer overflows/underflows.

   TODO: 
     - instrument loads that return memory addresses .
*/

#include "seahorn/Transforms/Instrumentation/BufferBoundsCheck.hh"
#include "seahorn/Analysis/CanAccessMemory.hh"

#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/CallSite.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/ADT/Statistic.h"

#include <boost/optional.hpp>

#include "avy/AvyDebug.h"

//#include "seahorn/Analysis/Steensgaard.hh"


namespace seahorn
{
  using namespace llvm;

  char BufferBoundsCheck::ID = 0;

  inline bool isUnknownSize (uint64_t sz) 
  { 
      return sz == AliasAnalysis::UnknownSize; 
  }
        
  inline bool isScalarGlobal(const Value* V)
  {
    if (const GlobalVariable *GV = dyn_cast<GlobalVariable>(V)) 
    {
      return (GV->getType ()->getContainedType (0)->isFloatingPointTy() ||
              GV->getType ()->getContainedType (0)->isIntegerTy ());
    }
    else return false;
  }

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

  std::pair<Value*,Value*> 
  BufferBoundsCheck::findShadowArg (Function *F, const Value *Arg) 
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

  // For each function parameter for which we want to propagate its
  // offset and size we add two more *undefined* function parameters
  // for placeholding its offset and size which will be filled out
  // later.
  bool  BufferBoundsCheck::addFunShadowParams (Function *F, LLVMContext &ctx)  
  {
    if (F->isDeclaration ()) return false;

    if (F->getName ().equals ("main")) return false;

    // TODO: relax this case
    if (F->hasAddressTaken ()) return false;
    // TODO: relax this case
    const FunctionType *FTy = F->getFunctionType ();
    if (FTy->isVarArg ()) return false;

    CanAccessMemory &CM = getAnalysis<CanAccessMemory> ();
    if (!CM.canAccess(F)) return false;

    // copy params
    // AttributeSet PAL = F->getAttributes ();
    std::vector<llvm::Type*> ParamsTy (FTy->param_begin (), FTy->param_end ());
    // XXX: I use string because StringRef and Twine should not be
    //      stored.
    std::vector<std::string> NewNames;
    Function::arg_iterator FAI = F->arg_begin();
    for(FunctionType::param_iterator I =  FTy->param_begin (),             
            E = FTy->param_end (); I!=E; ++I, ++FAI) 
    {
      Type *PTy = *I;
      if (IsShadowableType (PTy))
      {
        ParamsTy.push_back (m_Int64Ty);
        Twine offset_name = FAI->getName () + ".shadow.offset";
        NewNames.push_back (offset_name.str ());
        // PAL = PAL.addAttribute(ctx, 
        //                        ParamsTy.size (), 
        //                        Attribute::ReadOnly);
        
        ParamsTy.push_back (m_Int64Ty);
        Twine size_name = FAI->getName () + ".shadow.size";
        NewNames.push_back (size_name.str ());
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
      Twine offset_name = retVal->getName () + ".shadow.ret.offset";
      NewNames.push_back (offset_name.str ());
      ParamsTy.push_back (m_Int64PtrTy);
      Twine size_name = retVal->getName () + ".shadow.ret.size";
      NewNames.push_back (size_name.str ());
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

      Value * storeOffset = getArgument (NF, NF->arg_size () - 2);
      Value * storeSize = getArgument (NF, NF->arg_size () - 1);
      B.CreateCall (m_memsafeFn, storeOffset);
      StoreInst* SI_Off = B.CreateStore (UndefValue::get (m_Int64Ty), storeOffset); 
      B.CreateCall (m_memsafeFn, storeSize);
      StoreInst* SI_Size = B.CreateStore (UndefValue::get (m_Int64Ty), storeSize); 
      m_ret_shadows [NF] = std::make_pair (SI_Off,SI_Size);
    }

    // Replace all callers
    while (!F->use_empty ())
    {
      // here we know all uses are call instructions
      CallSite CS (cast<Value>(F->user_back ()));

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
  
  // uint64_t BufferBoundsCheck::getDSNodeSize (const Value *V, DSGraph *dsg, DSGraph *gDsg)
  // {
  //   // DSNode* n = dsg->getNodeForValue (V).getNode ();
  //   // if (!n) n = gDsg->getNodeForValue (V).getNode ();
  //   // if (!n) return AliasAnalysis::UnknownSize;
  //   //m_dsa->print (errs (), NULL);
  //   //errs () << "Size: " << n->getSize () << "\n";
  //   //return n->getSize ();
  //   // TODO: n->getSize() doesn't return the expected size for arrays.
  //   return AliasAnalysis::UnknownSize;
  // }

  Value* BufferBoundsCheck::createAdd(IRBuilder<>B, 
                                      Value *LHS, Value *RHS, 
                                      const Twine &Name)
  {
    assert (LHS->getType ()->isIntegerTy () && 
            RHS->getType ()->isIntegerTy ());

    Value *LHS1 = B.CreateZExtOrBitCast (LHS, m_Int64Ty);
    Value *RHS1 = B.CreateZExtOrBitCast (RHS, m_Int64Ty);

    return  B.CreateAdd ( LHS1, RHS1, Name);
  }

  Value* BufferBoundsCheck::createMul(IRBuilder<>B, 
                                      Value *LHS, unsigned RHS, 
                                      const Twine &Name)
  {
    assert (LHS->getType ()->isIntegerTy ());

    Value* LHS1 = B.CreateZExtOrBitCast (LHS, m_Int64Ty );

    return  B.CreateMul ( LHS1, 
                          ConstantInt::get (m_Int64Ty, RHS), 
                          Name);
  }


  void BufferBoundsCheck::resolvePHIUsers (const Value *v, 
                                           DenseMap <const Value*, Value*>& m_table)
  {
    // resolve phi incoming values that were marked as undef
    for (Value::const_use_iterator it = v->use_begin(), et = v->use_end (); it!=et; ++it)
    {
      if (const PHINode *PHI = dyn_cast<PHINode> (*it))
      {
        Value * ValShadow = m_table [*it];
        if (!ValShadow) continue;

        if (PHINode *PHIShadow = dyn_cast<PHINode> (ValShadow))
        {
          for (unsigned i=0; i < PHI->getNumIncomingValues (); i++)
          {
            if (PHI->getIncomingValue (i) == v && 
                ( ( i >= PHIShadow->getNumIncomingValues ()) ||
                  PHIShadow->getIncomingValue (i) == UndefValue::get (m_Int64Ty)))
            {
              LOG ("boc", errs () << "Resolving " << *PHIShadow << "\n");
              PHIShadow->setIncomingValue (i, m_table [v]);
              LOG ("boc", errs () << "Replacing undef with " << *(m_table [v]) << "\n");
            }
          }
        }        
      }
    }
    
  }

  void BufferBoundsCheck::instrumentGepOffset(IRBuilder<> B, 
                                              Instruction* insertPoint,                                    
                                              const GetElementPtrInst *gep)
  {
    LOG ("boc" , errs () << "instrumenting GEP (offset) : " << *gep << "\n");

    SmallVector<const Value*, 4> ps;
    SmallVector<const Type*, 4> ts;
    gep_type_iterator typeIt = gep_type_begin (*gep);
    for (unsigned i = 1; i < gep->getNumOperands (); ++i, ++typeIt)
    {
      ps.push_back (gep->getOperand (i));
      ts.push_back (*typeIt);
    }

    const Value *base = gep->getPointerOperand ();    

    Value *gepBaseOff = m_offsets [base];

    if (!gepBaseOff)
    {
      LOG ("boc", errs () << "Cannot determine the base offset for ";
           errs () << *base << "\n");
      return;
    }

    B.SetInsertPoint(insertPoint);
    
    Value* curVal = gepBaseOff;

    LOG ("boc", errs() << "Offset=" << *curVal << " "); 

    for (unsigned i = 0; i < ps.size (); ++i)
    {
      if (const StructType *st = dyn_cast<const StructType> (ts [i]))
      {
        if (const ConstantInt *ci = dyn_cast<const ConstantInt> (ps [i]))
        {
          unsigned off = fieldOffset (st, ci->getZExtValue ());
          curVal = createAdd( B, 
                              curVal, 
                              ConstantInt::get (m_Int64Ty, off));

          LOG ("boc", errs ()  << " + " << off );
        }
        else assert (false);
      }
      else if (const SequentialType *seqt = dyn_cast<const SequentialType> (ts [i]))
      {
        // arrays, pointers, and vectors

        unsigned sz = storageSize (seqt->getElementType ());

        LOG ("boc", errs () << " + " << " (" << *ps[i]  << " * " << sz << ") ");

        Value *LHS = curVal;

        Value *RHS = createMul(B, 
                               const_cast<Value*> (ps[i]), 
                               sz);

        curVal = createAdd(B, LHS, RHS); 
                           
      }
    } 
    LOG ("boc", errs () << "\n");

    m_offsets [gep] = curVal;                                   
    
    resolvePHIUsers (gep, m_offsets);
  }


  /*

    This instruments the offset and size of ptr by inserting
    arithmetic instructions. We instrument ptr as long as it follows a
    sequence of instructions with this grammar:

    Ptr = globalVariable | alloca | malloc | load | inttoptr | formal param | return |
          (getElementPtr (Ptr) | bitcast (Ptr) | phiNode (Ptr) ... (Ptr) )*  

   */
  void BufferBoundsCheck::instrumentSizeAndOffsetPtr (Function *F,
                                                      IRBuilder<> B, 
                                                      Instruction* insertPoint, 
                                                      const Value * ptr,
                                                      ValueSet &visited
                                                      /*DSGraph *dsg, DSGraph *gDsg*/)
  {

    if (visited.find(ptr) != visited.end ())  return;
    visited.insert (ptr);
    
    /// recursive cases 

    if (const BitCastInst *Bc = dyn_cast<BitCastInst> (ptr))
    {

      Instruction *insertPoint = const_cast<Instruction*> (cast<Instruction> (Bc));

      instrumentSizeAndOffsetPtr (F, B, insertPoint, 
                                  Bc->getOperand (0),
                                  visited
                                  /*,dsg, gDsg*/);
      
      B.SetInsertPoint(insertPoint);

      if (Value* shadowBcOpOff = lookupOffset(Bc->getOperand (0)))
        m_offsets [ptr] = shadowBcOpOff;

      if (Value* shadowBcOpSize = lookupSize(Bc->getOperand (0)))
        m_sizes [ptr] = shadowBcOpSize;

      return;
    }

    if (const GetElementPtrInst *Gep = dyn_cast<GetElementPtrInst> (ptr))
    {

      Instruction *insertPoint = const_cast<Instruction*> (cast<Instruction> (Gep));

      instrumentSizeAndOffsetPtr (F, B, insertPoint, 
                                  Gep->getPointerOperand (),
                                  visited
                                  /*,dsg, gDsg*/);
      
      B.SetInsertPoint(insertPoint);

      instrumentGepOffset(B, insertPoint, Gep);
      
      if (Value* shadowGepOpSize = lookupSize(Gep->getPointerOperand ()))
      {
        m_sizes [ptr] = shadowGepOpSize;

        resolvePHIUsers (ptr, m_sizes);

        LOG ("boc", errs() << "Size=" << * (m_sizes [ptr]) << "\n"); 
      }

      return;
    }

    if (const PHINode *PHI = dyn_cast<PHINode> (ptr))
    {

      Instruction *insertPoint = const_cast<Instruction*> (cast<Instruction> (PHI));

      PHINode* shadowPHINodeOff = PHINode::Create (m_Int64Ty, PHI->getNumIncomingValues (), 
                                                   ((ptr->hasName ()) ? 
                                                    ptr->getName () + ".shadow.offset" : ""),
                                                   insertPoint);

      PHINode* shadowPHINodeSize = PHINode::Create (m_Int64Ty, PHI->getNumIncomingValues (), 
                                                    ((ptr->hasName ()) ? 
                                                     ptr->getName () + ".shadow.size" : ""),
                                                    insertPoint);

      for (unsigned i=0; i < PHI->getNumIncomingValues (); i++)
      {
        // placeholder for now
        shadowPHINodeOff->addIncoming (UndefValue::get (m_Int64Ty), PHI->getIncomingBlock (i));
        shadowPHINodeSize->addIncoming (UndefValue::get (m_Int64Ty), PHI->getIncomingBlock (i));
      }

      
      m_offsets [ptr] = shadowPHINodeOff;
      m_sizes [ptr] = shadowPHINodeSize;

      for (unsigned i=0; i < PHI->getNumIncomingValues (); i++)
      {

        Instruction *insertPoint = dyn_cast<Instruction> (PHI->getIncomingValue (i)); 
        if (!insertPoint)
          insertPoint = PHI->getIncomingBlock (i)->getFirstNonPHI ();

        instrumentSizeAndOffsetPtr (F, B, insertPoint, 
                                    PHI->getIncomingValue (i),
                                    visited
                                    /*,dsg, gDsg*/);


        if (Value* shadowPHIValOff = lookupOffset(PHI->getIncomingValue (i)))
        {
          //shadowPHINodeOff->addIncoming (shadowPHIValOff, PHI->getIncomingBlock (i));
          shadowPHINodeOff->setIncomingValue (i, shadowPHIValOff);
          LOG ("boc", errs() << "Offset=" << *shadowPHIValOff << "\n"); 
        }
        // else
        // {
        //   // placeholder to be resolved later to break cycle
        //   Value *Undef = UndefValue::get (m_Int64Ty);
        //   shadowPHINodeOff->addIncoming (Undef, PHI->getIncomingBlock (i));
        // }

        if (Value* shadowPHIValSize = lookupSize(PHI->getIncomingValue (i)))
        {
          //shadowPHINodeSize->addIncoming (shadowPHIValSize, PHI->getIncomingBlock (i));
          shadowPHINodeSize->setIncomingValue (i, shadowPHIValSize);
          LOG ("boc", errs() << "Offset=" << *shadowPHIValSize << "\n"); 
        }
        // else
        // {
        //   // placeholder to be resolved later to break cycle
        //   Value *Undef = UndefValue::get (m_Int64Ty);
        //   shadowPHINodeSize->addIncoming (Undef, PHI->getIncomingBlock (i));
        // }
      }

      return;
    }

    /// base cases
    
    if (isa<AllocaInst> (ptr) || 
        isa<GlobalVariable> (ptr) || 
        isa<LoadInst> (ptr) ||
        isAllocationFn (ptr, m_tli, true))
    {

      m_offsets [ptr] = ConstantInt::get (m_Int64Ty, 0);

      uint64_t Size = AliasAnalysis::UnknownSize;
      getObjectSize(ptr, Size, m_dl, m_tli, false);
      if (!isUnknownSize(Size))
      {
        m_sizes [ptr] = ConstantInt::get (m_Int64Ty,Size);
        return;
      }     

      // if (isa<AllocaInst> (ptr) || isa<GlobalVariable> (ptr))
      // {
      //   Size = getDSNodeSize(ptr, dsg, gDsg);
      //   if (!isUnknownSize(Size))
      //   {
      //     m_sizes [ptr] = ConstantInt::get (m_Int64Ty, Size);            
      //     return;
      //   }
      // }        
          
      // if (const LoadInst *load = dyn_cast<LoadInst> (ptr))
      // {
      //   Size = getDSNodeSize(load->getOperand (0), dsg, gDsg);
      //   if (!isUnknownSize(Size))
      //   {
      //     m_sizes [ptr] = ConstantInt::get (m_Int64Ty, Size);            
      //     return;
      //   }
      // }

      if (CallInst * MallocInst = extractMallocCall (const_cast<Value*> (ptr),
                                                     m_tli))
        {
          if (MallocInst->getNumArgOperands () == 1)
          {
            Value *mallocArg = MallocInst->getArgOperand(0);

            // Size = getDSNodeSize(mallocArg, dsg, gDsg);
            // if (!isUnknownSize(Size))
            // {
            //   m_sizes [ptr] = ConstantInt::get (m_Int64Ty, Size);            
            //   return;
            // }

            if (mallocArg->getType ()->isIntegerTy ())
            {
              m_sizes [ptr] = mallocArg;
              return;
            }
          }
        }     
    }

    if (const IntToPtrInst *IP = dyn_cast<IntToPtrInst> (ptr))
    {
      m_offsets [ptr] = ConstantInt::get (m_Int64Ty, 0);
      unsigned Size = m_dl->getPointerTypeSizeInBits (IP->getType ());
      m_sizes [ptr] = ConstantInt::get (m_Int64Ty, Size);
      return;
    }
    
    
    /// ptr is the return value of a call site      
    if (const CallInst *CI = dyn_cast<CallInst> (ptr))
    {
      CallSite CS (const_cast<CallInst*> (CI));
      Function *cf = CS.getCalledFunction ();      
      if (cf && IsShadowableFunction (*cf))
      {
        Value* ShadowRetOff  = CS.getArgument (CS.arg_size () - 2);
        Value* ShadowRetSize = CS.getArgument (CS.arg_size () - 1);

        B.SetInsertPoint(const_cast<CallInst*> (CI)); //just before CI
        auto it = B.GetInsertPoint ();
        ++it; // just after CI
        B.SetInsertPoint (const_cast<BasicBlock*>(CI->getParent ()), it);

        B.CreateCall (m_memsafeFn, ShadowRetOff);
        m_offsets [ptr] = B.CreateLoad (ShadowRetOff); 
        B.CreateCall (m_memsafeFn, ShadowRetSize);
        m_sizes [ptr] = B.CreateLoad (ShadowRetSize); 
        return;
      }
    }
    
    /// try if ptr is  a function formal parameter
    auto p =  findShadowArg (F, ptr);
    Value* shadowPtrOff =  p.first;
    Value* shadowPtrSize = p.second;
    if (shadowPtrOff && shadowPtrSize)
    {
      m_offsets [ptr] = shadowPtrOff;
      m_sizes [ptr] = shadowPtrSize;      
      return;
    }
    
    LOG( "boc", 
         errs () << "Unable to instrument " << *ptr << "\n");
  }

  void BufferBoundsCheck::instrumentSizeAndOffsetPtr (Function *F, IRBuilder<> B, 
                                                      Instruction* insertPoint, 
                                                      const Value * ptr
                                                      /*,DSGraph *dsg, DSGraph *gDsg*/)
  {
    ValueSet visited;
    instrumentSizeAndOffsetPtr (F, B, insertPoint, ptr, visited/*, dsg, gDsg*/);
  }

  //! instrument check for load, store and memset
  bool BufferBoundsCheck::instrumentCheck (IRBuilder<> B, 
                                           Instruction& inst, 
                                           const Value& ptr)
  {

    Value *ptrSize   = m_sizes [&ptr];
    Value *ptrOffset = m_offsets [&ptr];

    if (!(ptrSize && ptrOffset))
    {
      ChecksUnable++;
      return false;
    }

    B.SetInsertPoint (&inst);    

    // It's tempting to generate Cmp1 and Cmp2 and conjoin them in an
    // And instruction. However, this is not code that we want to give
    // to a standard abstract interpreter.
    
    /// Underflow: add check ptrOffset >= 0 
    
    BasicBlock *OldBB0 = inst.getParent ();
    BasicBlock *Cont0 = OldBB0->splitBasicBlock(B.GetInsertPoint ());
    OldBB0->getTerminator ()->eraseFromParent ();
    BranchInst::Create (Cont0, OldBB0);
    
    B.SetInsertPoint (Cont0->getFirstNonPHI ());    
    
    Value* Cmp1 = B.CreateICmpSGE (ptrOffset, 
                                   ConstantInt::get (m_Int64Ty, 0),
                                   "BOA_underflow");
    
    BasicBlock *OldBB1 = Cont0;
    BasicBlock *Cont1 = OldBB1->splitBasicBlock(B.GetInsertPoint ());
    OldBB1->getTerminator ()->eraseFromParent();
    BranchInst::Create (Cont1, m_err_bb, Cmp1, OldBB1);
    
    /// Overflow: add check ptrOffset < ptrSize 
    
    B.SetInsertPoint (Cont1->getFirstNonPHI ());    
    
    Value* Cmp2 = B.CreateICmpSLT (ptrOffset, 
                                   ptrSize, 
                                   "BOA_overflow");
    
    BasicBlock *OldBB2 = Cont1;
    BasicBlock *Cont2 = OldBB2->splitBasicBlock(B.GetInsertPoint ());
    OldBB2->getTerminator ()->eraseFromParent();
    BranchInst::Create (Cont2, m_err_bb, Cmp2, OldBB2);
    
    ChecksAdded++;

    LOG ("boc" , errs () << "\nInserted:\n";
         errs () << "\t" << "assert(" << *ptrOffset << " >= 0)\n";
         errs () << "\t" << "assert(" << *ptrOffset << " < " << *ptrSize << ")\n");
    
    return true;
  }


  //! instrument check for memcpy and memmove
  bool BufferBoundsCheck::instrumentCheck (IRBuilder<> B, 
                                           Instruction& inst, 
                                           const Value& ptr,
                                           const Value& len)
  {

    Value *ptrSize   = m_sizes [&ptr];
    Value *ptrOffset = m_offsets [&ptr];

    if (!(ptrSize && ptrOffset))
    {
      ChecksUnable++;
      return false;
    }

    B.SetInsertPoint (&inst);    
    
    BasicBlock *OldBB0 = inst.getParent ();
    BasicBlock *Cont0 = OldBB0->splitBasicBlock(B.GetInsertPoint ());
    OldBB0->getTerminator()->eraseFromParent ();
    BranchInst::Create(Cont0, OldBB0);
    
    B.SetInsertPoint (Cont0->getFirstNonPHI ());    

    // check underflow ptrOffset >= 0
    Value* Cmp1 = B.CreateICmpSGE (ptrOffset, 
                                   ConstantInt::get (m_Int64Ty, 0),
                                   "BOA_underflow");
    
                                      
    BasicBlock *OldBB1 = Cont0;
    BasicBlock *Cont1 = OldBB1->splitBasicBlock(B.GetInsertPoint ());
    OldBB1->getTerminator()->eraseFromParent();
    BranchInst::Create(Cont1, m_err_bb, Cmp1, OldBB1);

    /// Add check ptrOffset + len <= ptrSize

    B.SetInsertPoint (Cont1->getFirstNonPHI ());    

    Value *rng = createAdd (B, ptrOffset, const_cast<Value*> (&len));
    Value* Cmp2 = B.CreateICmpSLE (rng, ptrSize, "BOA_overflow");

    BasicBlock *OldBB2 = Cont1;
    BasicBlock *Cont2 = OldBB2->splitBasicBlock(B.GetInsertPoint ());
    OldBB2->getTerminator ()->eraseFromParent();
    BranchInst::Create (Cont2, m_err_bb, Cmp2, OldBB2);
        
    ChecksAdded++;

    LOG ("boc" , errs () << "\nInserted:\n";
         errs () 
         << "\t" << "assert(" << *ptrOffset << " >= 0 \n"
         << "\t" << "assert(" << *ptrOffset << " + " << len 
         << " <= " << *ptrSize << ")\n");
    
    return true;
  }

  void BufferBoundsCheck::instrumentErrAndSafeBlocks (IRBuilder<>B, 
                                                      Function &F)
  {

    LLVMContext &ctx = B.getContext ();

    m_err_bb = BasicBlock::Create(ctx, "Error", &F);
    B.SetInsertPoint (m_err_bb);    
    B.CreateCall (m_errorFn);
    B.CreateUnreachable ();
    return;

    // // The original return statement is replaced with a block with an
    // // infinite loop while a fresh block named ERROR returning an
    // // arbitrary value is created. All unsafe checks jump to ERROR.
    // // The original program has been fully inlined and the only
    // // function is "main" which should return an integer.

    // BasicBlock * retBB = nullptr;
    // ReturnInst *retInst = nullptr;
    // for (BasicBlock& bb : F)
    // {
    //   TerminatorInst * inst = bb.getTerminator ();
    //   if (inst && (retInst = dyn_cast<ReturnInst> (inst))) 
    //   {
    //     retBB = &bb;
    //     break;
    //   }
    // }

    // if (!retInst)
    // {     
    //   if (F.getReturnType ()->isIntegerTy ())
    //   {
    //     m_err_bb = BasicBlock::Create(ctx, "Error", &F);
    //     B.SetInsertPoint (m_err_bb);    
    //     B.CreateRet ( ConstantInt::get (F.getReturnType (), 42)); 
                                        
    //   }
    //   else
    //     assert (false && 
    //             "Only instrument functions that return an integer");
    // }
    // else
    // {
    //   Value * retVal = retInst->getReturnValue ();
      
    //   if (retVal && retVal->getType ()->isIntegerTy ())
    //   {
    //     m_err_bb = BasicBlock::Create(ctx, "ERROR", &F);
    //     B.SetInsertPoint (m_err_bb);    
    //     B.CreateRet ( ConstantInt::get (retVal->getType (), 42));
                                        
    //   }
    //   else 
    //   {
    //     assert ( false &&
    //             "Only instrument functions that return an integer");
    //   }

    //   // replace original return with an infinite loop
      
    //   B.SetInsertPoint (retInst);    
    //   BasicBlock::iterator It = B.GetInsertPoint ();
    //   m_safe_bb = retBB->splitBasicBlock(It, "SAFE");
    //   BranchInst *loopInst = BranchInst::Create(m_safe_bb);
    //   ReplaceInstWithInst(retInst, loopInst);
    // }
  }

  bool BufferBoundsCheck::runOnFunction (Function &F)
  {
    if (F.isDeclaration ()) return false;

    // DSGraph* dsg = m_dsa->getDSGraph (F);
    // if (!dsg) return false;
    // DSGraph* gDsg = dsg->getGlobalsGraph ();

    LLVMContext &ctx = F.getContext ();
    IRBuilder<> B (ctx);
      
    instrumentErrAndSafeBlocks (B,F);
    assert (m_err_bb);

    std::vector<Instruction*> WorkList;
    for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) 
    {
      Instruction *I = &*i;
      if (isa<LoadInst> (I) || isa<StoreInst>  (I) || 
          isa<CallInst> (I) || isa<ReturnInst> (I))
        WorkList.push_back(I);
    }


    bool change = false;
    bool is_memsafe = false;
    for (auto inst : WorkList)
    {
      if (const CallInst *CI = dyn_cast<CallInst> (inst))
      {
        CallSite CS (const_cast<CallInst*> (CI));
        const Function *cf = CS.getCalledFunction ();
        if (cf)
        { 
          if (cf->getName ().startswith ("verifier.memsafe"))
          {  is_memsafe = true; }
          else if (cf->getName ().startswith ("llvm.memcpy") || 
                   cf->getName ().startswith ("llvm.memmove"))
          {
            LOG ("boc" , 
                 errs () << "\n ================= \n";
                 errs () << "Found memcpy/memmove: " << *inst << "\n");

            Value* DestPtr = CS.getArgument (0);
            Value* SrcPtr  = CS.getArgument (1);
            Value* Len     = CS.getArgument (2);            

            instrumentSizeAndOffsetPtr (&F, B, inst, SrcPtr);
            instrumentSizeAndOffsetPtr (&F, B, inst, DestPtr);

            change |=  instrumentCheck (B, *inst, *SrcPtr, *Len);           
            change |=  instrumentCheck (B, *inst, *DestPtr, *Len);           
          }
          else if (cf->getName ().startswith ("llvm.memset"))

          {
            LOG ("boc" , 
                 errs () << "\n ================= \n";
                 errs () << "Found memset: " << *inst << "\n");

            Value* DestPtr = CS.getArgument (0);
            Value* Len    = CS.getArgument (2);            

            instrumentSizeAndOffsetPtr (&F, B, inst, DestPtr);
            change |=  instrumentCheck (B, *inst, *DestPtr, *Len);           
          }
          else 
          {
            // Resolving the shadow offsets and sizes which are
            // actual parameters of a function call
            //
            // At this point F has this form:
            //
            // q = foo (p,...,_,_,&q.off,&q.size);
              //
            // The placeholders are filled out with the shadow
            // variables corresponding to p.
            if (IsShadowableFunction (*cf))
            {
              size_t orig_arg_size = getOrigArgSize (*cf);
              unsigned shadow_idx = orig_arg_size;
              for (size_t idx= 0; idx < orig_arg_size; idx++)
              {
                const Value* ArgPtr = CS.getArgument (idx);
                // this could be a symptom of a bug
                if (isa<UndefValue> (ArgPtr) || isa<ConstantPointerNull> (ArgPtr))
                  continue;
                if (IsShadowableType (ArgPtr->getType ()))
                {
                  instrumentSizeAndOffsetPtr (&F, B, inst, ArgPtr);                  
                  Value *ptrSize   = m_sizes [ArgPtr];
                  Value *ptrOffset = m_offsets [ArgPtr];
                  if (ptrSize && ptrOffset)
                  {
                    CS.setArgument (shadow_idx, ptrOffset);
                    CS.setArgument (shadow_idx+1, ptrSize);
                    change = true;
                  }
                  shadow_idx +=2;
                }
              }
            }
          }
        }
      }
      else if (const ReturnInst *ret = dyn_cast<ReturnInst> (inst))
      {
        if (const Value* retVal = ret->getReturnValue ())
        {
          if (IsShadowableType (retVal->getType ()))
          { // Resolving the shadow offset and size of the return
            // value of a function. At this point, F has this form:
            //    ...
            //    *p.off = _;
            //    *p.size = _;
            //    return p;
            // 
            // The placeholders _ are filled out with the shadow
            // variables associated with the return variable.
            instrumentSizeAndOffsetPtr (&F, B, inst, retVal);                  
            Value *ShadowOffset = m_offsets [retVal];
            Value *ShadowSize = m_sizes [retVal];
            if (ShadowOffset && ShadowSize) {
              auto p = findShadowRet (&F);
              if (p.first) 
                p.first->setOperand (0, ShadowOffset);
              if (p.second) 
                p.second->setOperand (0, ShadowSize);
              change |= (p.first || p.second);
              }
          }
        }
      }
      else if (const LoadInst *load = dyn_cast<LoadInst> (inst))
      {
        if (is_memsafe)
        { // a load inserted by intrumentation which is known as safe
          is_memsafe = false;
          continue;
        }

        LOG ("boc" , 
             errs () << "\n ================= \n";
             errs () << "Found load: " << *inst << "\n");

        const Value * Ptr = load->getOperand (0);
        if (isScalarGlobal (Ptr))
        {
          LOG ("boc", errs () << "Skipped load from scalar global " << *Ptr << "\n");
          ChecksSkipped++;
        }
        else
        {
          instrumentSizeAndOffsetPtr (&F, B, inst, Ptr/*, dsg, gDsg*/);
          change |=  instrumentCheck (B, *inst, *Ptr);           
        }
      }
      else if (const StoreInst *store = dyn_cast<StoreInst> (inst))
      {
        if (is_memsafe)
        { // a store inserted by intrumentation which is known as safe
          is_memsafe = false;
          continue;
        }

        LOG ("boc" , 
             errs () << "\n ================= \n";
             errs () << "Found store: " << *inst << "\n");


        const Value * Ptr = store->getOperand (1);
        if (isScalarGlobal (Ptr)) 
        {
          LOG ("boc", errs () << "Skipped store to scalar global " << *Ptr << "\n");
          ChecksSkipped++;
        }
        else
        {
          instrumentSizeAndOffsetPtr (&F, B, inst, Ptr/*, dsg, gDsg*/);
          change |=  instrumentCheck (B, *inst, *Ptr); 
        }
      }
    }
    
    return change;
  }

  bool BufferBoundsCheck::runOnModule (llvm::Module &M)
  {
    if (M.begin () == M.end ()) return false;
      
    m_dl = &getAnalysis<DataLayoutPass>().getDataLayout ();

    m_tli = &getAnalysis<TargetLibraryInfo>();

    //m_dsa = &getAnalysis<SteensgaardDataStructures> ();

    LLVMContext &ctx = M.getContext ();

    // ObjectSizeOffsetEvaluator TheObjSizeEval (m_dl, m_tli, ctx, true);
    // m_obj_size_eval = &TheObjSizeEval;

    m_Int64Ty = Type::getInt64Ty (ctx);
    m_Int64PtrTy = m_Int64Ty->getPointerTo ();
      
    AttrBuilder B;
    B.addAttribute (Attribute::NoReturn);
    // B.addAttribute (Attribute::ReadNone);
    
    AttributeSet as = AttributeSet::get (ctx, 
                                         AttributeSet::FunctionIndex,
                                         B);
    
    m_errorFn = dyn_cast<Function>
        (M.getOrInsertFunction ("verifier.error",
                                as,
                                Type::getVoidTy (ctx), NULL));
    
    B.clear ();
    B.addAttribute (Attribute::ReadNone);
    as = AttributeSet::get (ctx, 
                            AttributeSet::FunctionIndex,
                            B);
    
    m_memsafeFn = dyn_cast<Function>
        (M.getOrInsertFunction ("verifier.memsafe",
                                as,
                                Type::getVoidTy (ctx), 
                                m_Int64PtrTy,                
                                NULL));
    
    bool change = false;

    /* First, we shadow function parameters */
    std::vector<Function*> oldFuncs;
    for (Function &F : M) 
      oldFuncs.push_back (&F);

    for (auto F: oldFuncs) 
      change |= addFunShadowParams (F, ctx);

    /* Second, we shadow load/store pointers */
    for (Function &F : M) 
      change |= runOnFunction (F); 

    errs () << "-- Added  " << ChecksAdded << " buffer overflow/underflow checks.\n" 
            << "-- Missed " << ChecksUnable << " checks.\n";

    return change;
  }
    
  void BufferBoundsCheck::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    //AU.addRequiredTransitive<llvm::SteensgaardDataStructures> ();
    AU.addRequired<llvm::DataLayoutPass>();
    AU.addRequired<llvm::TargetLibraryInfo>();
    AU.addRequired<llvm::UnifyFunctionExitNodes> ();
    AU.addRequired<CanAccessMemory> ();
  } 

}

static llvm::RegisterPass<seahorn::BufferBoundsCheck> 
X ("boc", "Insert buffer overflow/underflow checks");
 

  

