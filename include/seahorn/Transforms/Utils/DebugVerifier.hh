#pragma once

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace seahorn {
/// Runs module verification and terminates when verification fails.
/// Additionally, the passes counter can be used to track the different
/// instances of the verifier pass.
llvm::ModulePass *createDebugVerifierPass(int instanceID);
} // namespace seahorn
