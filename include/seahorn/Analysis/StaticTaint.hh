#pragma once 

#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/DenseSet.h"

namespace seahorn {

class StaticTaint : public llvm::ModulePass {
  llvm::DenseSet<llvm::Value*> m_taint;
  bool m_bPrintAnalysis;
  llvm::DenseSet<llvm::CallInst*> m_tainted;

  llvm::DominatorTreeBase<llvm::BasicBlock, true> m_dm;

  void taintBB(llvm::BasicBlock &BB);

public:
  static char ID;

  StaticTaint(bool print = false) :
	  llvm::ModulePass(ID),
	  m_bPrintAnalysis(print),
	  m_dm() {}

  bool isTainted(llvm::Value *v) { return m_taint.find(v) != m_taint.end(); }

  virtual bool runOnModule(llvm::Module &M) override;
  void runOnFunction(llvm::Function &F);
  bool runOnBasicBlock(llvm::BasicBlock &B);

  void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  llvm::StringRef getPassName() const override { return "StaticTaint"; }
};
}

