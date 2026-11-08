// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#ifndef __SORT_TOPO_HH_
#define __SORT_TOPO_HH_

#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/IR/Function.h"

namespace seahorn {
using namespace llvm;

void RevTopoSort(const llvm::Function &F, std::vector<const BasicBlock *> &out);
} // namespace seahorn

#endif
