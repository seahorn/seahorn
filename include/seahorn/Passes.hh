#ifndef SEAHORN_PASSES__HH_
#define SEAHORN_PASSES__HH_

#include "llvm/Pass.h"
namespace seahorn
{
  llvm::Pass* createMarkInternalInlinePass ();
  llvm::Pass* createNondetInitPass ();
  llvm::Pass* createDeadNondetElimPass ();
  llvm::Pass* createDummyExitBlockPass ();

  llvm::Pass* createLoadIkosPass ();
  llvm::Pass* createShadowMemDsaPass ();
}

#endif /* SEAHORN_PASSES__HH_ */
