#include "seahorn/Transforms/Utils/RemoveUnreachableBlocksPass.hh"
#include "llvm/Transforms/Utils/Local.h"

#include "seahorn/config.h"

#include "seadsa/ShadowMem.hh"
#include "seadsa/DsaAnalysis.hh"

using namespace llvm;

namespace seahorn
{
  char RemoveUnreachableBlocksPass::ID = 0;

  bool RemoveUnreachableBlocksPass::runOnFunction (Function &F)
  {return removeUnreachableBlocks (F);}

  void RemoveUnreachableBlocksPass::getAnalysisUsage (AnalysisUsage &AU) const {
      // Preserve Sea-DSA passes
      AU.addPreservedID(seadsa::DsaAnalysis::ID);
      AU.addPreservedID(seadsa::ShadowMemPass::ID);      
  }
}

namespace seahorn {
    Pass* createRemoveUnreachableBlocksPass()
    {return new RemoveUnreachableBlocksPass();}
}


// --- new pass manager wrapper ---
#include "seahorn/SeaNewPmPasses.hh"
llvm::PreservedAnalyses
seahorn::SeaRemoveUnreachableBlocksPass::run(llvm::Function &F, llvm::FunctionAnalysisManager &) {
  return RemoveUnreachableBlocksPass().runOnFunction(F) ? llvm::PreservedAnalyses::none()
                            : llvm::PreservedAnalyses::all();
}
