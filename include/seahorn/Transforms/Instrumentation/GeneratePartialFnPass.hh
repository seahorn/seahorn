#pragma once

/**
 * Locates external function calls annotated by "partial" and generates
 * placeholder implementations.
 */

#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

using namespace llvm;

namespace seahorn {

// Returns true if GeneratePartialFnPass has marked F as a stub of a partial
// function.
bool isInferable(const Function &F);

// Returns true if F has the "partial" annotation.
bool isPartialFn(const Function &F);

} // namespace seahorn
