#pragma once

#include "llvm/IR/Module.h"

namespace llvm {
class TargetLibraryInfoWrapperPass;
} // namespace llvm

namespace seadsa {
class GlobalAnalysis;
} // namespace seadsa

namespace clam {
class CrabBuilderManager;
class InterGlobalClam;
} // namespace clam

namespace seahorn {
class CrabAnalysis {
  //// \brief crab's cfg builder manager
  std::unique_ptr<clam::CrabBuilderManager> m_cfg_builder_man;
  //// \brief crab instance
  std::unique_ptr<clam::InterGlobalClam> m_crab;

  /// \brief Creates a crab's cfg builder manager
  void initCrabAnalysis(const llvm::Module &M, seadsa::GlobalAnalysis &dsa,
                        llvm::TargetLibraryInfoWrapperPass &tliPass);
  /// \brief Run crab analysis
  void runCrabAnalysis();

public:
  CrabAnalysis() {}
  void runCrabAnalysisOnModule(const llvm::Module &M,
                               seadsa::GlobalAnalysis &dsa,
                               llvm::TargetLibraryInfoWrapperPass &tliPass);
  const clam::InterGlobalClam &getCrab() const;
  clam::InterGlobalClam &getCrab();
};
} // namespace seahorn

