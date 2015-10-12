#ifndef SEAHORN_PASSES__HH_
#define SEAHORN_PASSES__HH_

#include "seahorn/config.h"
#include "llvm/Pass.h"
namespace seahorn
{
  llvm::Pass* createMarkInternalInlinePass ();
  llvm::Pass* createNondetInitPass ();
  llvm::Pass* createDeadNondetElimPass ();
  llvm::Pass* createDummyExitBlockPass ();
  llvm::Pass* createExternalizeAddressTakenFunctionsPass (); 

  llvm::Pass* createLoadCrabPass ();
  llvm::Pass* createShadowMemDsaPass ();
  llvm::Pass * createStripShadowMemPass ();

  llvm::Pass* createCutLoopsPass ();
  llvm::Pass* createMarkFnEntryPass ();

  llvm::Pass* createPromoteMallocPass ();
  llvm::Pass* createKillVarArgFnPass ();
  
  llvm::Pass* createStripLifetimePass ();
  llvm::Pass* createStripUselessDeclarationsPass ();
}

#ifdef HAVE_LLVM_SEAHORN
#include "llvm_seahorn/Transforms/Scalar.h"
namespace seahorn
{
  inline llvm::FunctionPass* createInstCombine ()
  {return llvm_seahorn::createInstructionCombiningPass ();}
}
#else
#include "llvm/Transforms/Scalar.h"
namespace seahorn
{
  inline llvm::FunctionPass* createInstCombine()
  {return llvm::createInstructionCombiningPass ();}
}
#endif

#endif /* SEAHORN_PASSES__HH_ */
