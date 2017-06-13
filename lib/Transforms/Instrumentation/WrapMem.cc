/**
SeaHorn Verification Framework
Copyright (c) 2015 Carnegie Mellon University.
All Rights Reserved.

THIS SOFTWARE IS PROVIDED "AS IS," WITH NO WARRANTIES
WHATSOEVER. CARNEGIE MELLON UNIVERSITY EXPRESSLY DISCLAIMS TO THE
FULLEST EXTENT PERMITTEDBY LAW ALL EXPRESS, IMPLIED, AND STATUTORY
WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, AND
NON-INFRINGEMENT OF PROPRIETARY RIGHTS.

Released under a modified BSD license, please see license.txt for full
terms.

DM-0002198
*/

#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"


#include "seahorn/config.h"
#ifdef HAVE_DSA
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "dsa/DSNode.h"
#include "dsa/Steensgaard.hh"
#endif

#define DEBUG_TYPE "wrap-mem"

using namespace llvm;

namespace
{
  class WrapMem : public ModulePass
  {
#ifdef HAVE_DSA
    DataStructures *m_dsa;
#endif
    
    const DataLayout *m_dl;
    IntegerType *m_intPtrTy;
    Function *m_memLoad;
    Function *m_memStore;
    
  public:
    static char ID;
    WrapMem() : ModulePass (ID) {}

    bool runOnModule (Module &M)
    {
#ifdef HAVE_DSA
      m_dsa = &getAnalysis<EQTDDataStructures> ();
      //m_dsa = &getAnalysis<SteensgaardDataStructures> ();
#endif
      LLVMContext &C = M.getContext ();
      m_dl = &M.getDataLayout ();
      m_intPtrTy = m_dl->getIntPtrType (C, 0);
      
      /* void __sea_mem_load (void* dst, void* src, size_t sz)
         { memcpy (dst, src, sz); }
       */
      m_memLoad = cast<Function> (M.getOrInsertFunction ("__seahorn_mem_load",
                                                         Type::getVoidTy (C),
                                                         Type::getInt8PtrTy (C, 0),
                                                         Type::getInt8PtrTy (C, 0),
                                                         m_intPtrTy,
                                                         NULL));
      /* void __sea_mem_store (void *src, void *dst, size_t sz)
         { memcpy (dst, src, sz); }
      */
      m_memStore = cast<Function> (M.getOrInsertFunction ("__seahorn_mem_store",
                                                          Type::getVoidTy (C),
                                                          Type::getInt8PtrTy (C, 0),
                                                          Type::getInt8PtrTy (C, 0),
                                                          m_intPtrTy,
                                                          NULL));
      for (Function &F : M)
        runOnFunction (F);
      return true;
    }

    bool runOnFunction (Function &F)
    {
      if (F.isDeclaration () || F.empty ()) return false;

#ifdef HAVE_DSA
      DSGraph *dsg = m_dsa->getDSGraph (F);
#endif
      IRBuilder<> B(F.getContext ());
      Type* i8PtrTy = B.getInt8PtrTy ();
      for (BasicBlock &bb : F)
        for (Instruction &inst : bb)
        {
          if (LoadInst *load = dyn_cast<LoadInst> (&inst))
          {
#ifdef HAVE_DSA
            if (dsg)
            {
              DSNodeHandle &nh = dsg->getNodeForValue (load->getPointerOperand ());
              DSNode *n = nh.getNode ();
              if (!n) continue;
              // TODO: fine tune what nodes might be interesting to wrap
              if (!n->isExternalNode ()) continue;
            }
#endif
            B.SetInsertPoint (load);
            AllocaInst *x = B.CreateAlloca (load->getType ()); 
            uint64_t sz = m_dl->getTypeStoreSize (load->getType ());
            B.CreateCall (m_memLoad,
			  {B.CreateBitCast (x, i8PtrTy),
			   B.CreateBitCast (load->getPointerOperand (), i8PtrTy),
			   ConstantInt::get (m_intPtrTy, sz)});
            load->setOperand (load->getPointerOperandIndex (), x);
          }
          else if (StoreInst *store = dyn_cast<StoreInst> (&inst))
          {
#ifdef HAVE_DSA
            if (dsg)
            {
              DSNodeHandle &nh = dsg->getNodeForValue (store->getPointerOperand ());
              DSNode *n = nh.getNode ();
              if (!n) continue;
              // TODO: fine tune what nodes might be interesting to wrap
              if (!n->isExternalNode ()) continue;
            }
#endif
            B.SetInsertPoint (store);
            AllocaInst *x = B.CreateAlloca (store->getValueOperand ()->getType ());
            B.SetInsertPoint (store->getNextNode ());
            uint64_t sz = m_dl->getTypeStoreSize (store->getValueOperand ()->getType ());
            B.CreateCall (m_memStore,
			  {B.CreateBitCast (x, i8PtrTy),
			   B.CreateBitCast (store->getPointerOperand (), i8PtrTy),
			   ConstantInt::get (m_intPtrTy, sz)});
            store->setOperand (store->getPointerOperandIndex (), x);
          }
        }
      
      return true;
    }

    void getAnalysisUsage (AnalysisUsage &AU) const
    {
#ifdef HAVE_DSA
      AU.addRequired<llvm::EQTDDataStructures>();
      // AU.addRequiredTransitive<llvm::SteensgaardDataStructures> ();
#endif
      AU.setPreservesAll();
    }
    
  };
  char WrapMem::ID = 0;
}

namespace seahorn
{
  Pass *createWrapMemPass() { return new WrapMem(); }
}

static RegisterPass<WrapMem> X("wrap-mem-pass",
                               "Wrap external memory accesses with custom functions");

