#ifndef _CRAB_ANALYSIS_HH_
#define _CRAB_ANALYSIS_HH_

#include "llvm/IR/Module.h"

namespace llvm {
class TargetLibraryInfoWrapperPass;
} // namespace llvm

namespace seadsa {
class ShadowMem;
} // namespace seadsa

namespace clam {
class CrabBuilderManager;
class InterGlobalClam;
} // namespace clam

namespace seahorn {
using namespace llvm;

class CrabAnalysis {
  //// \brief crab's cfg builder manager
  std::unique_ptr<clam::CrabBuilderManager> m_cfg_builder_man;
  //// \brief crab instance to solve alloc bounds
  std::shared_ptr<clam::InterGlobalClam> m_crab;

  /// \brief Creates a crab's cfg builder manager
  void initCrabAnalysis(const llvm::Module &M, seadsa::ShadowMem &dsaPass,
                        llvm::TargetLibraryInfoWrapperPass &tliPass);
  /// \brief Run crab analysis
  void runCrabAnalysis();

public:
  CrabAnalysis() {}
  void runCrabAnalysisOnModule(const llvm::Module &M,
                               seadsa::ShadowMem &dsaPass,
                               llvm::TargetLibraryInfoWrapperPass &tliPass);
  std::shared_ptr<clam::InterGlobalClam> getCrab() { return m_crab; }
};
} // namespace seahorn

#endif /* _CRAB_ANALYSIS_HH_ */
