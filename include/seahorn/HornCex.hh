#ifndef _HORN_CEX__HH_
#define _HORN_CEX__HH_

#include "seahorn/Bmc.hh"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace seahorn {
using namespace llvm;

/*
 * Reconstructs a counterexample from HornSolver
 */
class HornCex : public llvm::ModulePass {
public:
  static char ID;

  HornCex() : ModulePass(ID) {}
  virtual ~HornCex() {}

  virtual bool runOnModule(Module &M) override;
  virtual bool runOnFunction(Module &M, Function &F);
  virtual void getAnalysisUsage(AnalysisUsage &AU) const override;
  virtual StringRef getPassName() const override { return "HornCex"; }
};
} // namespace seahorn

#endif
