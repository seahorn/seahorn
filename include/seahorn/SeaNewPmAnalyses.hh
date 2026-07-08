#pragma once
/// New-PM analysis wrappers for SeaHorn's legacy analysis passes. Each Result
/// owns a legacy state-holder object (constructed standalone and driven via
/// its runImpl), following sea-dsa's DsaInfoAnalysis pattern. Consumers fetch
/// results from the analysis managers instead of getAnalysis<>.

#include "llvm/IR/PassManager.h"

#include "seahorn/Analysis/CanFail.hh"
#include "seahorn/Analysis/CutPointGraph.hh"
#include "seahorn/Analysis/TopologicalOrder.hh"

#include <memory>

namespace seahorn {

/// Module analysis: which functions may reach a failure. Wraps CanFail.
class CanFailAnalysis : public llvm::AnalysisInfoMixin<CanFailAnalysis> {
  friend llvm::AnalysisInfoMixin<CanFailAnalysis>;
  static llvm::AnalysisKey Key;

public:
  using Result = std::unique_ptr<seahorn::CanFail>;
  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
};

/// Function analysis: reverse-topological block order.
class TopologicalOrderAnalysis
    : public llvm::AnalysisInfoMixin<TopologicalOrderAnalysis> {
  friend llvm::AnalysisInfoMixin<TopologicalOrderAnalysis>;
  static llvm::AnalysisKey Key;

public:
  using Result = std::unique_ptr<seahorn::TopologicalOrder>;
  Result run(llvm::Function &F, llvm::FunctionAnalysisManager &FAM);
};

/// Function analysis: the cut-point graph over the topological order.
class CutPointGraphAnalysis
    : public llvm::AnalysisInfoMixin<CutPointGraphAnalysis> {
  friend llvm::AnalysisInfoMixin<CutPointGraphAnalysis>;
  static llvm::AnalysisKey Key;

public:
  using Result = std::unique_ptr<seahorn::CutPointGraph>;
  Result run(llvm::Function &F, llvm::FunctionAnalysisManager &FAM);
};

} // namespace seahorn
