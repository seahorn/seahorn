#ifndef REMOVEUNREACHABLEBLOCKSPASS_H
#define REMOVEUNREACHABLEBLOCKSPASS_H

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"

namespace seahorn
{
  using namespace llvm;
  
  struct RemoveUnreachableBlocksPass : public FunctionPass
  {
    static char ID;
    RemoveUnreachableBlocksPass () : FunctionPass (ID) {}
    
    bool runOnFunction (Function &F) override;
    void getAnalysisUsage (AnalysisUsage &AU) const override;

    StringRef getPassName() const override {
      return "RemoveUnreachableBlockPass";
    }

  };
}

#endif /* REMOVEUNREACHABLEBLOCKSPASS_H */
