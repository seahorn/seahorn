#pragma once

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"

#include <memory>
#include <vector>

namespace seahorn {

class ControlDependenceAnalysis;

class ControlDependenceAnalysisPass : public llvm::FunctionPass {
public:
  static char ID;

  ControlDependenceAnalysisPass() : llvm::FunctionPass(ID) {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  virtual bool runOnFunction(llvm::Function &F) override;

  llvm::StringRef getPassName() const override { return "ControlDependenceAnalysisPass"; }
  void print (llvm::raw_ostream &os, const llvm::Module *M) const override;

  ControlDependenceAnalysis& getControlDependenceAnalysis() {
    assert(m_analysis);
    return *m_analysis;
  }

private:
  std::unique_ptr<ControlDependenceAnalysis> m_analysis;
};

llvm::FunctionPass *createControlDependenceAnalysisPass();

struct CDInfo {
  llvm::BasicBlock *CDBlock;
  llvm::Value *Condition;

  bool operator==(const CDInfo &other) const {
    return CDBlock == other.CDBlock;
  }
};

class ControlDependenceAnalysis {
public:
  virtual ~ControlDependenceAnalysis() = default;

  virtual llvm::ArrayRef<CDInfo> getCDBlocks(llvm::BasicBlock *BB) const = 0;
  virtual bool
  isReachable(llvm::BasicBlock *Src, llvm::BasicBlock *Dst) const = 0;
  virtual unsigned getBBTopoIdx(llvm::BasicBlock *BB) const = 0;
};

}

