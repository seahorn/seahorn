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

/// A pass to replace all variadic functions by their declarations

#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

namespace {
using namespace llvm;
class KillVarArgFn : public ModulePass {
public:
  static char ID;

  KillVarArgFn() : ModulePass(ID) {}

  virtual bool runOnModule(Module &M) override {
    bool changed = false;
    for (auto &F : M)
      if (F.isVarArg()) {
        F.deleteBody();
        F.setComdat(nullptr);
        changed = true;
      }

    return changed;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
  }
};

char KillVarArgFn::ID = 0;
} // namespace

namespace seahorn {
Pass *createKillVarArgFnPass() { return new KillVarArgFn(); }
} // namespace seahorn

static llvm::RegisterPass<KillVarArgFn> X("kill-vaarg",
                                          "Remove variadic functions");
