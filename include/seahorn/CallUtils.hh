#pragma once
#include "llvm/IR/InstrTypes.h"

namespace seahorn {
inline const llvm::Function *getCalledFunction(const llvm::CallBase &CB) {
  auto *V = CB.getCalledOperand();
  return V ? llvm::dyn_cast<llvm::Function>(V->stripPointerCasts()) : nullptr;
}
} // namespace seahorn
