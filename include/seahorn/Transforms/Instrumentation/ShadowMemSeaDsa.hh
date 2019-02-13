/// This file should be completely moved into C++ file.
#pragma once
#include "llvm/Pass.h"

namespace llvm {
class Value;
}
#define USE_NEW_SHADOW_SEA_DSA 1
namespace seahorn {
class ShadowMemSeaDsa : public llvm::ModulePass {
public:
  static char ID;
  ShadowMemSeaDsa() : llvm::ModulePass(ID) {}

  bool runOnModule(llvm::Module &M) override;

  bool runOnFunction(llvm::Function &F);
  void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  llvm::StringRef getPassName() const override { return "ShadowMemDsa2"; }
};

bool isShadowMemInst(const llvm::Value *v);

} // namespace seahorn
