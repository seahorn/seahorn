#pragma once
/// Export to sea-mlir and the sea-mlir BMC engine.
///
/// The exporter prints the function BMC would check (after SeaHorn's
/// pipeline, with shadow memory) as a `sea.program` in sea-mlir's textual
/// format. It prints text by hand: SeaHorn does not link MLIR. Unsupported
/// input is an error, never skipped silently.
///
/// The engine (--horn-bmc-engine=sea-mlir) exports, runs sea-vc on the
/// result, and reports sat/unsat like the mono BMC engine.

#include "llvm/IR/PassManager.h"

#include <cstdint>
#include <map>
#include <string>

namespace llvm {
class Function;
class Instruction;
class Module;
class raw_ostream;
} // namespace llvm

namespace seahorn {

/// What each nondet site of an exported program stands for (for replaying
/// sea-mlir counterexamples in SeaHorn).
struct SeaMlirSites {
  /// site -> the LLVM instruction (nondet call, alloca, memhavoc, ...) or
  /// null for sites that stand for a whole memory region.
  std::map<uint64_t, const llvm::Instruction *> inst;
};

/// Prints \p F as a sea.program. Returns false after reporting errors if
/// \p F uses something the exporter does not support.
bool exportSeaMlir(const llvm::Function &F, llvm::raw_ostream &out,
                   SeaMlirSites &sites);

/// --horn-bmc-engine=sea-mlir: export main, run sea-vc, print sat/unsat.
class SeaMlirEnginePass : public llvm::PassInfoMixin<SeaMlirEnginePass> {
  bool m_solve;

public:
  explicit SeaMlirEnginePass(bool solve) : m_solve(solve) {}
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

} // namespace seahorn
