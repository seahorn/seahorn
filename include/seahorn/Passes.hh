/**
SeaHorn Verification Framework
Copyright (c) 2016 Carnegie Mellon University.
All Rights Reserved.

THIS SOFTWARE IS PROVIDED "AS IS," WITH NO WARRANTIES
WHATSOEVER. CARNEGIE MELLON UNIVERSITY EXPRESSLY DISCLAIMS TO THE
FULLEST EXTENT PERMITTEDBY LAW ALL EXPRESS, IMPLIED, AND STATUTORY
WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, AND
NON-INFRINGEMENT OF PROPRIETARY RIGHTS.

Released under a modified BSD license, please see license.txt for full
terms.

DM-0002198
*/

#ifndef SEAHORN_PASSES__HH_
#define SEAHORN_PASSES__HH_

#include "seahorn/config.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

namespace seahorn
{
  llvm::Pass* createMarkInternalInlinePass ();
  llvm::Pass* createNondetInitPass ();
  llvm::Pass* createDeadNondetElimPass ();
  llvm::Pass* createDummyExitBlockPass ();
  llvm::Pass* createExternalizeAddressTakenFunctionsPass (); 
  llvm::Pass* createDevirtualizeFunctionsPass (); 
  llvm::Pass* createPromoteMemoryToRegisterPass (); 

  llvm::Pass* createLoadCrabPass ();
  llvm::Pass* createShadowMemDsaPass ();
  llvm::Pass* createStripShadowMemPass ();

  llvm::Pass* createCutLoopsPass ();
  llvm::Pass* createMarkFnEntryPass ();

  llvm::Pass* createPromoteMallocPass ();
  llvm::Pass* createKillVarArgFnPass ();
  
  llvm::Pass* createStripLifetimePass ();
  llvm::Pass* createStripUselessDeclarationsPass ();

  llvm::Pass* createPromoteBoolLoadsPass ();

  llvm::Pass* createEnumVerifierCallsPass ();

  llvm::Pass* createCanReadUndefPass ();

  llvm::Pass* createBmcPass (llvm::raw_ostream* out, bool solve);

  llvm::Pass* createProfilerPass();
  llvm::Pass* createCFGPrinterPass ();
  llvm::Pass* createCFGOnlyPrinterPass ();
  llvm::Pass* createCFGViewerPass ();
  llvm::Pass* createCFGOnlyViewerPass ();
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
