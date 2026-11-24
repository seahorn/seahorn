// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
// Static scalar globals in the sea-mlir export (default: a dropped
// initializer is an error). sp is a unique scalar: the shadow memory gives it
// no shadow.mem.global.init, and LowerGvInitializers stores its initializer
// at the start of main; si is promoted to a stack slot. Neither initializer
// is dropped, and the export succeeds.
// RUN: %sea yama -y sea-mlir-export --bound=1 -m64 --horn-sea-mlir-out=%t.mlir "%s" 2>&1 | filecheck %s
// RUN: filecheck %s --check-prefix=MLIR < %t.mlir
// CHECK-NOT: dropped
// CHECK-NOT: Error
// CHECK: sea-mlir-export: wrote
// MLIR: %[[SP:v[0-9]+]] = sea.global @"sp"
// MLIR-NEXT: %[[NULL:v[0-9]+]] = sea.ptr.null
// MLIR-NEXT: sea.store %{{v[0-9]+}}[%[[SP]]], %[[NULL]]

extern int nd_int(void);
extern void __VERIFIER_error(void);
#define sassert(x)                                                             \
  if (!(x))                                                                    \
  __VERIFIER_error()

static unsigned char const *sp;
static int si = 7;
static void bump(void) { si += nd_int(); }
int tgt;

int main(void) {
  if (nd_int())
    sp = (unsigned char const *)&tgt;
  if (nd_int())
    bump();
  sassert(sp == 0 || *sp == 0 || si != 7);
  return 0;
}
