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
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &);
};

class PromoteBoolLoadsPass : public llvm::PassInfoMixin<PromoteBoolLoadsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &);
};

class LowerArithWithOverflowIntrinsicsPass
    : public llvm::PassInfoMixin<LowerArithWithOverflowIntrinsicsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &);
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
  llvm::PreservedAnalyses run(llvm::Function &,
                              llvm::FunctionAnalysisManager &);
};

class DummyMainFunctionPass
    : public llvm::PassInfoMixin<DummyMainFunctionPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class ExternalizeFunctionsPass
    : public llvm::PassInfoMixin<ExternalizeFunctionsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class ExternalizeAddressTakenFunctionsPass
    : public llvm::PassInfoMixin<ExternalizeAddressTakenFunctionsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class KillVarArgFnPass : public llvm::PassInfoMixin<KillVarArgFnPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class MarkInternalInlinePass
    : public llvm::PassInfoMixin<MarkInternalInlinePass> {
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

class LowerGvInitializersPass
    : public llvm::PassInfoMixin<LowerGvInitializersPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class LowerConstantExprsPass
    : public llvm::PassInfoMixin<LowerConstantExprsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class SeaRemoveUnreachableBlocksPass
    : public llvm::PassInfoMixin<SeaRemoveUnreachableBlocksPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &,
                              llvm::FunctionAnalysisManager &);
};

class PromoteMemcpyPass : public llvm::PassInfoMixin<PromoteMemcpyPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &,
                              llvm::FunctionAnalysisManager &);
};

class SimplifyPointerLoopsPass
    : public llvm::PassInfoMixin<SimplifyPointerLoopsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &,
                              llvm::FunctionAnalysisManager &);
};

class BranchSentinelPass : public llvm::PassInfoMixin<BranchSentinelPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &,
                              llvm::FunctionAnalysisManager &);
};

class BackEdgeCutterPass : public llvm::PassInfoMixin<BackEdgeCutterPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &,
                              llvm::FunctionAnalysisManager &);
};

class LowerIsDerefPass : public llvm::PassInfoMixin<LowerIsDerefPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &,
                              llvm::FunctionAnalysisManager &);
};

class FatBufferBoundsCheckPass
    : public llvm::PassInfoMixin<FatBufferBoundsCheckPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &,
                              llvm::FunctionAnalysisManager &);
};

class EnumVerifierCallsPass
    : public llvm::PassInfoMixin<EnumVerifierCallsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class NullCheckPass : public llvm::PassInfoMixin<NullCheckPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class LowerLibCxxAbiFunctionsPass
    : public llvm::PassInfoMixin<LowerLibCxxAbiFunctionsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class SliceFunctionsPass : public llvm::PassInfoMixin<SliceFunctionsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class LowerAssertPass : public llvm::PassInfoMixin<LowerAssertPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class StripLifetimeNewPass
    : public llvm::PassInfoMixin<StripLifetimeNewPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class OneAssumePerBlockNewPass
    : public llvm::PassInfoMixin<OneAssumePerBlockNewPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class GeneratePartialFnNewPass
    : public llvm::PassInfoMixin<GeneratePartialFnNewPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class PromoteVerifierCallsPass
    : public llvm::PassInfoMixin<PromoteVerifierCallsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class MarkInternalAllocOrDeallocInlinePass
    : public llvm::PassInfoMixin<MarkInternalAllocOrDeallocInlinePass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class SymbolizeConstantLoopBoundsPass
    : public llvm::PassInfoMixin<SymbolizeConstantLoopBoundsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &,
                              llvm::FunctionAnalysisManager &);
};

class RenameNondetPass : public llvm::PassInfoMixin<RenameNondetPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class KleeInternalizePass : public llvm::PassInfoMixin<KleeInternalizePass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class StripUselessDeclarationsPass
    : public llvm::PassInfoMixin<StripUselessDeclarationsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class DevirtFunctionsPass : public llvm::PassInfoMixin<DevirtFunctionsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class CrabLowerIsDerefPass : public llvm::PassInfoMixin<CrabLowerIsDerefPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class MixedSemanticsPass : public llvm::PassInfoMixin<MixedSemanticsPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class AbstractMemoryPass : public llvm::PassInfoMixin<AbstractMemoryPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class SeaStripDeadDebugInfoPass
    : public llvm::PassInfoMixin<SeaStripDeadDebugInfoPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class SimpleMemoryCheckPass
    : public llvm::PassInfoMixin<SimpleMemoryCheckPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class MarkInternalConstructOrDestructInlinePass
    : public llvm::PassInfoMixin<MarkInternalConstructOrDestructInlinePass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

class LowerThreadLocalAddressPass
    : public llvm::PassInfoMixin<LowerThreadLocalAddressPass> {
public:
  llvm::PreservedAnalyses run(llvm::Function &,
                              llvm::FunctionAnalysisManager &);
};

} // namespace seahorn
