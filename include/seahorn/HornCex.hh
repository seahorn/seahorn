#ifndef _HORN_CEX__HH_
#define _HORN_CEX__HH_

#include <functional>
#include "seahorn/Bmc.hh"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace seahorn {
using namespace llvm;

/*
 * Reconstructs a counterexample from HornSolver
 */
class HornifyModule;
class HornSolver;
class CanFail;
class HornCex : public llvm::ModulePass {
  HornifyModule *m_hm = nullptr;
  HornSolver *m_hs = nullptr;
  const CanFail *m_canFail = nullptr;
  std::function<const llvm::TargetLibraryInfo &(llvm::Function &)> m_tliGetter;

public:
  static char ID;

  HornCex() : ModulePass(ID) {}
  virtual ~HornCex() {}

  virtual bool runOnModule(Module &M) override;
  bool runImpl(Module &M, HornifyModule &hm, HornSolver &hs,
               const CanFail *canFail,
               std::function<const llvm::TargetLibraryInfo &(llvm::Function &)>
                   tliGetter);
  virtual bool runOnFunction(Module &M, Function &F);
  virtual void getAnalysisUsage(AnalysisUsage &AU) const override;
  virtual StringRef getPassName() const override { return "HornCex"; }
};
} // namespace seahorn

#endif
