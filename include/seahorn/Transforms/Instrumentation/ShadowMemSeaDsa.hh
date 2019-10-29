#pragma once
#include "llvm/IR/CallSite.h"
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


  // Obtain the bottom up dsa graph of the function
  sea_dsa::Graph & getSummaryGraph(const llvm::Function &F);
  bool hasSummaryGraph(const llvm::Function &F);

  sea_dsa::Graph & getDsaGraph(const llvm::Function &F);
  bool hasDsaGraph(const llvm::Function &F);

  // API of shadow mem instructions/shadow ids
  bool shadowInstrIsCallSiteParam(llvm::CallSite &cs);
  bool shadowInstrWrites(llvm::CallSite &cs);
  bool shadowInstrReads(llvm::CallSite &cs);
  llvm::Value * getShadowInAlloc(llvm::CallSite &cs);
  llvm::Value *getShadowOutAlloc(llvm::CallSite &cs);

  unsigned getShadowId(llvm::CallSite &cs);

  // API of graphs/shadow ids
  bool hasShadowId(const sea_dsa::Cell *);
  unsigned getCellShadowId(const sea_dsa::Cell &c);

  static const llvm::StringRef m_argNew;
  static const llvm::StringRef m_argRef;
  static const llvm::StringRef m_argMod;
  };

bool isShadowMemInst(const llvm::Value *v);

} // namespace seahorn
