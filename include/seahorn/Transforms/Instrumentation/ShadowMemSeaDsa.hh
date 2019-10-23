/// This file should be completely moved into C++ file.
// TODO: remove this comment now? we want to use this pass in the vcgen
#pragma once
#include "llvm/Pass.h"

#include "sea_dsa/Global.hh"
#include "sea_dsa/Graph.hh"

#include <memory>

namespace llvm {
class Value;
}

namespace {
// defined in ShadowMemSeaDsa.cc
class ShadowDsaImpl;
}

#define USE_NEW_SHADOW_SEA_DSA 1
namespace seahorn {

class ShadowMemSeaDsa : public llvm::ModulePass {

private:
  sea_dsa::GlobalAnalysis *m_dsa;
  std::unique_ptr<ShadowDsaImpl> m_shadow;

public:
  static char ID;
  ShadowMemSeaDsa();
  ~ShadowMemSeaDsa();

  bool runOnModule(llvm::Module &M) override;

  bool runOnFunction(llvm::Function &F);
  void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  llvm::StringRef getPassName() const override { return "ShadowMemSeaDsa"; }

  // TODO: should this be a cell?
  bool hasShadowId(const sea_dsa::Node *);
  unsigned getNodeShadowId(const sea_dsa::Node *);

  sea_dsa::Graph & getSummaryGraph(const llvm::Function &F);
  bool hasSummaryGraph(const llvm::Function &F);

  sea_dsa::Graph & getDsaGraph(const llvm::Function &F);
  bool hasDsaGraph(const llvm::Function &F);
};

bool isShadowMemInst(const llvm::Value *v);

} // namespace seahorn
