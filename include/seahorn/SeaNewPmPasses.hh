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

class NondetInitPass : public llvm::PassInfoMixin<NondetInitPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class DeadNondetElimPass : public llvm::PassInfoMixin<DeadNondetElimPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &, llvm::FunctionAnalysisManager &);
};

class DummyMainFunctionPass : public llvm::PassInfoMixin<DummyMainFunctionPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class ExternalizeFunctionsPass : public llvm::PassInfoMixin<ExternalizeFunctionsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class ExternalizeAddressTakenFunctionsPass : public llvm::PassInfoMixin<ExternalizeAddressTakenFunctionsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class KillVarArgFnPass : public llvm::PassInfoMixin<KillVarArgFnPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class MarkInternalInlinePass : public llvm::PassInfoMixin<MarkInternalInlinePass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class WrapMemPass : public llvm::PassInfoMixin<WrapMemPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class NameValuesPass : public llvm::PassInfoMixin<NameValuesPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class LowerGvInitializersPass : public llvm::PassInfoMixin<LowerGvInitializersPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class LowerConstantExprsPass : public llvm::PassInfoMixin<LowerConstantExprsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class SeaRemoveUnreachableBlocksPass : public llvm::PassInfoMixin<SeaRemoveUnreachableBlocksPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &, llvm::FunctionAnalysisManager &);
};

} // namespace seahorn
