// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
// A failed sea-mlir export ends `sea` with a nonzero status also without
// --horn-sea-mlir-export-only (the engine as verify-c-common runs it): sea-vc
// does not run, and no output file is left behind (a stale one is removed).
// The initializer of pp holds pointers: the export cannot write it.
// RUN: printf '#!/bin/sh\necho "sea-vc ran"\necho "result: unsat"\n' > %t.sh
// RUN: chmod +x %t.sh
// RUN: echo stale > %t.mlir
// RUN: not %sea bpf -O0 --bmc=mono --horn-bmc-engine=sea-mlir --horn-sea-vc=%t.sh --horn-sea-mlir-out=%t.mlir "%s" 2>&1 | filecheck %s
// RUN: not test -e %t.mlir
// CHECK: Error: sea-mlir export: the initializer of global pp is dropped
// CHECK: Error: sea-mlir engine: export failed
// CHECK-NOT: sea-vc ran
// CHECK-NOT: {{^unsat$}}

extern int nd_int(void);
extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define sassert(x)                                                             \
  if (!(x))                                                                    \
  __VERIFIER_error()

int tgt;
int *pp[2] = {&tgt, &tgt};

int main(void) {
  int k = nd_int();
  __VERIFIER_assume(k == 0 || k == 1);
  sassert(*pp[k] == tgt);
  return 0;
}
