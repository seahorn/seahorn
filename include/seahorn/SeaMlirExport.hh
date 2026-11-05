#pragma once
/// Export to sea-mlir and the sea-mlir BMC engine.
///
/// The exporter prints the function BMC would check (after SeaHorn's
/// pipeline, with shadow memory) as a `sea.program` in sea-mlir's textual
/// format. It prints text by hand: SeaHorn does not link MLIR. Unsupported
/// input is an error, never skipped silently.
///
/// The engine (--horn-bmc-engine=sea-mlir) exports, runs sea-vc on the
/// result, and reports sat/unsat like the mono BMC engine. With
/// --horn-sea-mlir-export-only it exports and exits: status 0 and
/// `sea-mlir-export: wrote <file>` if the export succeeded, status 1 and
/// `sea-mlir-export: export failed ...` otherwise.
///
/// When the front end has decided every assertion (main removed, or a main
/// that cannot reach seahorn.fail), the engine prints
/// `sea-mlir-export: no main after the pipeline (...)` (or `main cannot
/// reach seahorn.fail ...`) and writes a trivial program, `sea.assert` of
/// true before `sea.halt`, which sea-vc answers unsat; it is not an error.

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
/// \p F uses something the exporter does not support. With \p llvmLinks,
/// every op's location links to its LLVM instruction (fused<"llvm @f %bb
/// #i">), and an op without a source position gets its position in the
/// output, the file \p mlirPath (--horn-sea-mlir-ll-out).
bool exportSeaMlir(const llvm::Function &F, llvm::raw_ostream &out,
                   SeaMlirSites &sites, bool llvmLinks = false,
                   llvm::StringRef mlirPath = "");

/// --horn-bmc-engine=sea-mlir: export main, run sea-vc, print sat/unsat.
class SeaMlirEnginePass : public llvm::PassInfoMixin<SeaMlirEnginePass> {
  bool m_solve;

public:
  explicit SeaMlirEnginePass(bool solve) : m_solve(solve) {}
  llvm::PreservedAnalyses run(llvm::Module &, llvm::ModuleAnalysisManager &);
};

} // namespace seahorn
