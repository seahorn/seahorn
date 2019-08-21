#pragma once

#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#include <memory>

namespace seahorn {

class ControlDependenceAnalysis;

// Module pass because it is currently scheduled from BmcPass that is also a
// module pass -- there's a PassManager bug when scheduling function passes from
// module passes.
class ControlDependenceAnalysisPass : public llvm::ModulePass {
public:
  static char ID;

  ControlDependenceAnalysisPass() : llvm::ModulePass(ID) {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  bool runOnFunction(llvm::Function &F);
  bool runOnModule(llvm::Module &M) override;

  llvm::StringRef getPassName() const override {
    return "ControlDependenceAnalysisPass";
  }
  void print(llvm::raw_ostream &os, const llvm::Module *M) const override;

  bool hasAnalysisFor(const llvm::Function &F) const {
    return m_analyses.count(&F) > 0;
  }

  ControlDependenceAnalysis &
  getControlDependenceAnalysis(const llvm::Function &F) {
    assert(hasAnalysisFor(F));
    return *m_analyses[&F];
  }

private:
  // PIMPL idiom used here to minimize the amount of code in headers.
  llvm::DenseMap<const llvm::Function *,
                 std::unique_ptr<ControlDependenceAnalysis>>
      m_analyses;
};

llvm::ModulePass *createControlDependenceAnalysisPass();

/// Exposes Control Dependence Information on the basic-block-level.
/// A basic block X is control dependent on a basic block Y iff:
///   1) X != Y, and
///   2) there's some control flow from Y that reaches X, Y ~> X, and at least
///      one successor of Y can never reach X.
/// Additionally, the class exposes reachability information and topological
/// ordering of basic blocks.
///
/// Requires all invokes to be lowered to calls, so only branches and switches
/// are the only supported terminators.
class ControlDependenceAnalysis {
public:
  virtual ~ControlDependenceAnalysis() = default;

  /// returns: All the blocks BB is control dependent-on. The returned array
  ///          is sorted in reverse-topological order as blocks appear in the
  ///          CFG.
  virtual llvm::ArrayRef<llvm::BasicBlock *>
  getCDBlocks(llvm::BasicBlock *BB) const = 0;
  /// \brief Returns true if there is a CFG path from Src to Dst
  virtual bool isReachable(llvm::BasicBlock *Src,
                           llvm::BasicBlock *Dst) const = 0;
  /// \brief Returns internal id of a basic block
  ///
  /// Ensures getBBTopoIdx(bb1) < getBBTopoIdx(bb2) ==> topo_lt(bb1, bb2)
  /// where topo_lt(x, y) the topological partial order on CFG
  virtual unsigned getBBTopoIdx(llvm::BasicBlock *BB) const = 0;
};

} // namespace seahorn
