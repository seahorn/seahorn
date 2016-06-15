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

#define DEBUG_TYPE "trap-mem"

using namespace llvm;

namespace
{
  class WrapMem : public ModulePass
  {
    const DataLayout *m_dl;
    IntegerType *m_intPtrTy;
    Function *m_memLoad;
    Function *m_memStore;
    
  public:
    static char ID;
    WrapMem() : ModulePass (ID) {}

    bool runOnModule (Module &M)
    {
      LLVMContext &C = M.getContext ();
      m_dl = &getAnalysis<DataLayoutPass> ().getDataLayout ();
      m_intPtrTy = m_dl->getIntPtrType (C, 0);
      
      m_memLoad = cast<Function> (M.getOrInsertFunction ("__sea_mem_load",
                                                         Type::getVoidTy (C),
                                                         Type::getInt8PtrTy (C, 0),
                                                         Type::getInt8PtrTy (C, 0),
                                                         m_intPtrTy,
                                                         NULL));
      m_memStore = cast<Function> (M.getOrInsertFunction ("__sea_mem_store",
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

      IRBuilder<> B(F.getContext ());
      Type* i8PtrTy = B.getInt8PtrTy ();
      for (BasicBlock &bb : F)
        for (Instruction &inst : bb)
        {
          if (LoadInst *load = dyn_cast<LoadInst> (&inst))
          {
            B.SetInsertPoint (load);
            AllocaInst *x = B.CreateAlloca (load->getType ()); 
            uint64_t sz = m_dl->getTypeStoreSize (load->getType ());
            B.CreateCall3 (m_memLoad,
                           B.CreateBitCast (x, i8PtrTy),
                           B.CreateBitCast (load->getPointerOperand (), i8PtrTy),
                           ConstantInt::get (m_intPtrTy, sz));
            load->setOperand (load->getPointerOperandIndex (), x);
          }
          else if (StoreInst *store = dyn_cast<StoreInst> (&inst))
          {
            B.SetInsertPoint (store);
            AllocaInst *x = B.CreateAlloca (store->getValueOperand ()->getType ());
            B.SetInsertPoint (store->getNextNode ());
            uint64_t sz = m_dl->getTypeStoreSize (store->getValueOperand ()->getType ());
            B.CreateCall3 (m_memStore, B.CreateBitCast (x, i8PtrTy),
                           B.CreateBitCast (store->getPointerOperand (), i8PtrTy),
                           ConstantInt::get (m_intPtrTy, sz));
            store->setOperand (store->getPointerOperandIndex (), x);
          }
        }
      
      return true;
    }

    void getAnalysisUsage (AnalysisUsage &AU) const
    {
      AU.addRequired<DataLayoutPass> ();
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

