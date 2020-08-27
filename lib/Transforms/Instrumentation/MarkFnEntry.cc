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

#define DEBUG_TYPE "mark-fn-entry"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {
/// Marks entry point of every function with a special call
class MarkFnEntry : public ModulePass {
  FunctionCallee m_mark;

public:
  static char ID;
  MarkFnEntry() : ModulePass(ID), m_mark(NULL) {}

  virtual bool runOnModule(Module &M) {

    m_mark = M.getOrInsertFunction("seahorn.fn.enter",
                                   Type::getVoidTy(M.getContext()));
    assert(isa<Function>(m_mark.getCallee()));
    cast<Function>(m_mark.getCallee())->setOnlyAccessesInaccessibleMemory();

    for (auto &F : M)
      runOnFunction(F);
    return true;
  }
  virtual bool runOnFunction(Function &F) {
    if (F.empty())
      return false;

    // -- insert call
    IRBuilder<> Builder(F.getContext());
    Builder.SetInsertPoint(&F.getEntryBlock(), F.getEntryBlock().begin());
    CallInst *call = Builder.CreateCall(m_mark);

    // -- find debug information if available
    for (auto &BB : F) {
      auto Inst =
          std::find_if(BB.begin(), BB.end(), [](const Instruction &Inst) {
            return !Inst.getDebugLoc().get();
          });
      if (Inst == BB.end())
        continue;

      // -- found instruction with a good debug location
      call->setDebugLoc(Inst->getDebugLoc());
      return true;
    }

    return true;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
  }
};

char MarkFnEntry::ID = 0;
} // namespace

namespace seahorn {
llvm::Pass *createMarkFnEntryPass() { return new MarkFnEntry(); }
} // namespace seahorn

static RegisterPass<MarkFnEntry> X("mark-fn-enter",
                                   "Mark function entry point");
