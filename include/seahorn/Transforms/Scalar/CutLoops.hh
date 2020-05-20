#pragma once

namespace llvm {
class Loop;
class LPPassManager;
class LoopInfo;
class ScalarEvolution;
class DominatorTree;
class AssumptionCache;
} // namespace llvm

namespace seahorn {
class SeaBuiltinsInfo;

/// Return true if the given loop can be cut
bool canCutLoop(llvm::Loop *L);

/// Cuts a given loop and removes it from loop managing passes
bool CutLoop(llvm::Loop *L, seahorn::SeaBuiltinsInfo &SBI,
             llvm::LPPassManager *LPM, llvm::LoopInfo *LI,
             llvm::ScalarEvolution *SE,
             llvm::DominatorTree *DT,
             llvm::AssumptionCache *AC);
} // namespace seahorn
