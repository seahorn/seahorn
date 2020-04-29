/**
SeaHorn Verification Framework
Copyright (c) 2016 Carnegie Mellon University.
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

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Support/raw_ostream.h"

#include <fstream>
#include <set>
#include <string>
using namespace llvm;

namespace {
class RenameNondet : public ModulePass {
  std::set<std::string> m_externalNames;
  const DataLayout *m_dl;
  TargetLibraryInfo *m_tli;
  StringMap<int> m_functionId;
  Module *m_module;
  SmallSet<Function *, 32> m_killFn;

  bool shouldRename(const GlobalValue &GV) {
    if (!GV.isDeclaration())
      return false;
    if (GV.getName().startswith("llvm."))
      return false;

    if (!m_tli)
      if (auto *Fn = dyn_cast<Function>(&GV))
        m_tli = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(*Fn);

    // -- known library function
    LibFunc F;
    if (m_tli && m_tli->getLibFunc(GV.getName(), F))
      return false;

    if (m_externalNames.count(GV.getName()) > 0)
      return false;

    return true;
  }

public:
  static char ID;
  RenameNondet() : ModulePass(ID), m_dl(nullptr), m_tli(nullptr) {

    // functions that are replaced by internalizer
    m_externalNames.insert("verifier.assume");
    m_externalNames.insert("verifier.assume.not");
    m_externalNames.insert("seahorn.fail");
    m_externalNames.insert("verifier.error");

    m_externalNames.insert("__VERIFIER_assume");
    m_externalNames.insert("__VERIFIER_error");

    m_externalNames.insert("__seahorn_get_value_i8");
    m_externalNames.insert("__seahorn_get_value_i16");
    m_externalNames.insert("__seahorn_get_value_i32");
    m_externalNames.insert("__seahorn_get_value_i64");
    m_externalNames.insert("__seahorn_get_value_ptr");

    m_externalNames.insert("__seahorn_mem_store");
    m_externalNames.insert("__seahorn_mem_load");

    // -- LLVM stuff
    m_externalNames.insert("llvm.used");
    m_externalNames.insert("llvm.dbg.declare");
    m_externalNames.insert("llvm.compiler.used");
    m_externalNames.insert("llvm.global_ctors");
    m_externalNames.insert("llvm.global_dtors");
    m_externalNames.insert("llvm.global.annotations");
    m_externalNames.insert("__stack_chk_fail");
    m_externalNames.insert("__stack_chk_guard");
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<TargetLibraryInfoWrapperPass>();
    AU.setPreservesAll();
  }

  bool runOnModule(Module &M) {
    m_module = &M;

    for (Function &F : M)
      if (!F.isDeclaration())
        runOnFunction(F);

    for (Function *F : m_killFn)
      F->eraseFromParent();
    return true;
  }

  bool runOnFunction(Function &F) {
    errs() << "Processing: " << F.getName() << "\n";
    Value *fname = nullptr;
    LLVMContext &C = F.getContext();
    IRBuilder<> Builder(C);
    SmallVector<Instruction *, 16> killList;
    for (BasicBlock &bb : F) {
      for (Instruction &inst : bb) {
        if (!isa<CallInst>(inst) && !isa<InvokeInst>(inst))
          continue;
        CallSite CS(&inst);
        Function *fn = CS.getCalledFunction();
        if (!fn)
          continue;

        if (shouldRename(*fn)) {
          errs() << "Renaming: " << fn->getName() << "\n";
          m_killFn.insert(fn);
          int id = m_functionId[fn->getName()];
          Function *newFn = cast<Function>(m_module->getOrInsertFunction(
              fn->getName().str() + "." + std::to_string(id),
              fn->getFunctionType()).getCallee());

          if (CallInst *CI = dyn_cast<CallInst>(&inst))
            CI->setCalledFunction(newFn);
          if (InvokeInst *II = dyn_cast<InvokeInst>(&inst))
            II->setCalledFunction(newFn);

          // CASE:  %_16 = bitcast i64 ()* @verifier.nondet.1 to i32 ()*
          m_functionId[fn->getName()]++;
        }
      }
    }
    return true;
  }
};

char RenameNondet::ID = 0;
} // namespace

namespace seahorn {
Pass *createRenameNondetPass() { return new RenameNondet(); }
} // namespace seahorn

static llvm::RegisterPass<RenameNondet>
    Y("rename-nondet-pass",
      "Assign a unique name to each non-determinism per call.");
