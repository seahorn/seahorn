// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
// Under -DVACCHECK sassert(X) emits __VERIFIER_assert(X) and a branch to
// __VERIFIER_error. The export drops the verifier.assert call without a
// warning and keeps the branch as sea.assert.
// RUN: %sea yama -y sea-mlir-export --bound=1 -m64 --horn-sea-mlir-out=%t.mlir -DVACCHECK "%s" 2>&1 | filecheck %s --check-prefix=LOG --allow-empty
// RUN: filecheck %s < %t.mlir
// LOG-NOT: verifier.assert
// CHECK: sea.assert

#include "seahorn/seahorn.h"
extern int nd_int(void);

int main(void) {
  int x = nd_int();
  assume(x > -5);
  sassert(x > 0);
  return 0;
}
