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

#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/config.h"
#define DEBUG_TYPE "wrap-mem"

using namespace llvm;

static llvm::cl::opt<bool> UseDsa(
    "horn-wrap-mem-dsa",
    llvm::cl::desc("Use DSA to choose which memory accesses should be wrapped"),
    llvm::cl::init(false));

namespace {
class WrapMem : public ModulePass {

  const DataLayout *m_dl;
  IntegerType *m_intPtrTy;
  FunctionCallee m_memLoad;
  FunctionCallee m_memStore;

public:
  static char ID;
  WrapMem() : ModulePass(ID) {}

  bool runOnModule(Module &M) {
    LLVMContext &C = M.getContext();
    m_dl = &M.getDataLayout();
    m_intPtrTy = m_dl->getIntPtrType(C, 0);

    /* void __sea_mem_load (void* dst, void* src, size_t sz)
       { memcpy (dst, src, sz); }
     */
    m_memLoad = M.getOrInsertFunction("__seahorn_mem_load", Type::getVoidTy(C),
                                      Type::getInt8PtrTy(C, 0),
                                      Type::getInt8PtrTy(C, 0), m_intPtrTy);
    /* void __sea_mem_store (void *src, void *dst, size_t sz)
       { memcpy (dst, src, sz); }
    */
    m_memStore = M.getOrInsertFunction(
        "__seahorn_mem_store", Type::getVoidTy(C), Type::getInt8PtrTy(C, 0),
        Type::getInt8PtrTy(C, 0), m_intPtrTy);

    if (Function *Main = M.getFunction("main")) {
      FunctionCallee memInit = M.getOrInsertFunction(
          "__seahorn_mem_init_routine", Type::getVoidTy(C));

      BasicBlock &entry = Main->getEntryBlock();
      IRBuilder<> B(M.getContext());
      B.SetInsertPoint(entry.getFirstNonPHI());
      B.CreateCall(memInit, {});
    }

    for (Function &F : M) {
      if (F.getName().equals("__seahorn_mem_init_routine")) {
        continue;
      }
      runOnFunction(F);
    }
    return true;
  }

  bool runOnFunction(Function &F) {
    if (F.isDeclaration() || F.empty())
      return false;

    LLVMContext &C = F.getContext();
    IRBuilder<> B(C);
    Type *i8PtrTy = B.getInt8PtrTy();
    for (BasicBlock &bb : F)
      for (Instruction &inst : bb) {
        if (LoadInst *load = dyn_cast<LoadInst>(&inst)) {
          B.SetInsertPoint(load);
          AllocaInst *x = B.CreateAlloca(load->getType());
          uint64_t sz = m_dl->getTypeStoreSize(load->getType());
          // uint64_t sz = load->getAlignment();
          B.CreateCall(m_memLoad,
                       {B.CreateBitCast(x, i8PtrTy),
                        B.CreateBitCast(load->getPointerOperand(), i8PtrTy),
                        ConstantInt::get(m_intPtrTy, sz)});
          load->setOperand(load->getPointerOperandIndex(), x);
        } else if (StoreInst *store = dyn_cast<StoreInst>(&inst)) {
          B.SetInsertPoint(store);
          AllocaInst *x = B.CreateAlloca(store->getValueOperand()->getType());
          B.SetInsertPoint(store->getNextNode());
          // uint64_t sz = store->getAlignment();
          uint64_t sz =
              m_dl->getTypeStoreSize(store->getValueOperand()->getType());
          B.CreateCall(m_memStore,
                       {B.CreateBitCast(x, i8PtrTy),
                        B.CreateBitCast(store->getPointerOperand(), i8PtrTy),
                        ConstantInt::get(m_intPtrTy, sz)});
          store->setOperand(store->getPointerOperandIndex(), x);
        }
      }

    return true;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const { AU.setPreservesAll(); }
};
char WrapMem::ID = 0;
} // namespace

namespace seahorn {
Pass *createWrapMemPass() { return new WrapMem(); }
} // namespace seahorn

static RegisterPass<WrapMem>
    X("wrap-mem-pass", "Wrap external memory accesses with custom functions");
