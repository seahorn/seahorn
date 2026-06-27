#pragma once
/// New pass manager versions of SeaHorn's preprocessing passes.
///
/// These are declared here (and defined alongside their legacy counterparts in
/// lib/) so seapp can build its pipeline with the new pass manager. The legacy
/// passes are kept for tools/pipelines that still use the legacy PM; both share
/// the same core transformation helpers.
#include "llvm/IR/PassManager.h"

namespace seahorn {

class PromoteSeahornAssumePass
    : public llvm::PassInfoMixin<PromoteSeahornAssumePass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &FAM);
};

class PromoteMallocPass : public llvm::PassInfoMixin<PromoteMallocPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &F, llvm::FunctionAnalysisManager &);
};

class PromoteBoolLoadsPass : public llvm::PassInfoMixin<PromoteBoolLoadsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &F, llvm::FunctionAnalysisManager &);
};

class LowerArithWithOverflowIntrinsicsPass
    : public llvm::PassInfoMixin<LowerArithWithOverflowIntrinsicsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &F, llvm::FunctionAnalysisManager &);
};

class CanReadUndefPass : public llvm::PassInfoMixin<CanReadUndefPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &);
};

class MarkFnEntryPass : public llvm::PassInfoMixin<MarkFnEntryPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &);
};

} // namespace seahorn
