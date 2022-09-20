#ifndef _HORN_CEX__HH_
#define _HORN_CEX__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/Bmc.hh"

namespace seahorn
{
  using namespace llvm;

  /*
   * Reconstructs a counterexample from HornSolver
   */
  class HornCex : public llvm::ModulePass {
  public:
    static char ID;
    
    HornCex () : ModulePass(ID) {}
    virtual ~HornCex () {}
    
    virtual bool runOnModule (Module &M) override;
    virtual bool runOnFunction (Module &M, Function &F);
    virtual void getAnalysisUsage (AnalysisUsage &AU) const override;
    virtual StringRef getPassName () const override {return "HornCex";}
  };
}

#endif
