#pragma once

#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstrTypes.h"

namespace seahorn {
inline const llvm::Function *getCalledFunction(const llvm::CallBase &CB) {
  auto *V = CB.getCalledOperand();
  return V ? dyn_cast<llvm::Function>(V->stripPointerCasts()) : nullptr;
}
inline const llvm::Function *getCalledFunction(const llvm::CallSite &CS) {
  auto *V = CS.getCalledValue();
  return V ? dyn_cast<llvm::Function>(V->stripPointerCasts()) : nullptr;
}
} // namespace seahorn
