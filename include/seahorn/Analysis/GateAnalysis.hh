#pragma once

#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#include <memory>

namespace seahorn {

class ControlDependenceAnalysis;
class GateAnalysis;

/// Pass for constructing (Thinned) Gated SSA form. Given a module with phi
/// nodes, it constructs gating gamma functions, and can express them as selects
/// in the LLVM IR. Note that if phi nodes are replaced with gammas the LLVM
/// module verifier can complain that uses of values in selects are not
/// dominated by their definition. However, this is fine in the (T)GSA form.
///
/// Loosely based on:
///   [1] Paul Havlak: Construction of Thinned Gated Single-Assignment Form.
///       LCPC 1993: 477-499,
///       https://pdfs.semanticscholar.org/55e2/51cc3ae1253443ac9a779de32474dd5e9a99.pdf
class GateAnalysisPass : public llvm::ModulePass {
public:
  static char ID;

  GateAnalysisPass() : llvm::ModulePass(ID) {}

  void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  bool runOnFunction(llvm::Function &F, ControlDependenceAnalysis &CDA);
  bool runOnModule(llvm::Module &M) override;

  llvm::StringRef getPassName() const override { return "GateAnalysisPass"; }
  void print(llvm::raw_ostream &os, const llvm::Module *M) const override;

  GateAnalysis &getGateAnalysis(const llvm::Function &F) {
    assert(m_analyses.count(&F) > 0);
    return *m_analyses[&F];
  }

private:
  llvm::DenseMap<const llvm::Function *, std::unique_ptr<GateAnalysis>>
      m_analyses;
};

llvm::ModulePass *createGateAnalysisPass();

class GateAnalysis {
public:
  virtual ~GateAnalysis() = default;

  /// returns: The gating gamma function. This will be either a gamma node
  ///         (SelectInst), another another value if the flow is not gated.
  virtual llvm::Value *getGamma(llvm::PHINode *PN) const = 0;

  /// return: Whether gamma nodes are Thinned (TGSA) or not (GSA). GSA allows
  ///         for Undefs to be used in gammas.
  virtual bool isThinned() const = 0;
};

} // namespace seahorn
