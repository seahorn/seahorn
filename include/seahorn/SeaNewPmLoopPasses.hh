#pragma once
/// New pass manager versions of SeaHorn's legacy LoopPasses.
///
/// These run under the new pass manager via
/// llvm::createFunctionToLoopPassAdaptor. They share the per-loop transform
/// logic (runImpl) with their legacy LoopPass counterparts; the legacy passes
/// are kept for tools/pipelines still on the legacy PM.
#include "llvm/Transforms/Scalar/LoopPassManager.h"

namespace seahorn {

class LoopPeelerNewPass : public llvm::PassInfoMixin<LoopPeelerNewPass> {
  unsigned m_Num;

public:
  LoopPeelerNewPass(unsigned Num = 0) : m_Num(Num) {}
  llvm::PreservedAnalyses run(llvm::Loop &L, llvm::LoopAnalysisManager &AM,
                              llvm::LoopStandardAnalysisResults &AR,
                              llvm::LPMUpdater &U);
};

class UnfoldLoopForDsaNewPass
    : public llvm::PassInfoMixin<UnfoldLoopForDsaNewPass> {
public:
  llvm::PreservedAnalyses run(llvm::Loop &L, llvm::LoopAnalysisManager &AM,
                              llvm::LoopStandardAnalysisResults &AR,
                              llvm::LPMUpdater &U);
};

} // namespace seahorn
