// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
// Global initializers in the sea-mlir export with memory SSA erased
// (--horn-sea-mlir-mem-ssa=erase): one seaimp.mem.fill per run of defined
// bytes (undef struct padding stays nondet, so the fill is split around it),
// at any size (big: more than 16 KiB, not one repeated byte; the default
// form, KEEP, makes the same fills as sea.mem.fill); an all-zero initializer
// stays one seaimp.memset; an initializer holding a pointer is still dropped
// (the same warning).
// RUN: %sea yama -y sea-mlir-export -O0 --bound=1 -m64 --horn-sea-mlir-allow-uninit-global=pp --horn-sea-mlir-out=%t.keep.mlir "%s" 2>&1 | filecheck %s --check-prefix=LOG
// RUN: filecheck %s --check-prefix=KEEP < %t.keep.mlir
// RUN: %sea yama -y sea-mlir-export -O0 --bound=1 -m64 --horn-sea-mlir-mem-ssa=erase --horn-sea-mlir-allow-uninit-global=pp --horn-sea-mlir-out=%t.mlir "%s" 2>&1 | filecheck %s --check-prefix=LOG
// RUN: filecheck %s < %t.mlir
// KEEP-DAG: %[[KBIG:v[0-9]+]] = sea.global @"big" size 20000 align 16
// KEEP-DAG: sea.mem.fill %{{v[0-9]+}}[%[[KBIG]]], dense<"0x01020000{{(00)+}}03"> : tensor<20000xi8> inplace : !sea.mem<!sea.ptr<64>, i8>
// KEEP-DAG: sea.mem.fill %{{v[0-9]+}}[%{{v[0-9]+}}], dense<[4, 3, 2, 1, 7, 0]> : tensor<6xi8> inplace : !sea.mem<!sea.ptr<64>, i8>
// KEEP-DAG: %[[KHI:v[0-9]+]] = sea.global @"hi" size 4 align 8
// KEEP-DAG: sea.mem.fill %{{v[0-9]+}}[%[[KHI]]], dense<[255, 128, 1, 127]> : tensor<4xi8> inplace : !sea.mem<!sea.ptr<64>, i8>
// KEEP-DAG: %[[KHB:v[0-9]+]] = sea.global @"hibig" size 300 align 16
// KEEP-DAG: sea.mem.fill %{{v[0-9]+}}[%[[KHB]]], dense<"0x80FF{{(00)+}}FE"> : tensor<300xi8> inplace : !sea.mem<!sea.ptr<64>, i8>
// KEEP: sea.assert
// LOG-NOT: global big
// LOG: Warning: sea-mlir export: the initializer of global pp is dropped (it holds pointers or constant expressions)
// LOG-NOT: global big
// LOG: sea-mlir-export: wrote
// CHECK-DAG: %[[BIG:v[0-9]+]] = seaimp.global %mem @"big" size 20000 align 16
// CHECK-DAG: seaimp.mem.fill %mem[%[[BIG]]], dense<"0x01020000{{(00)+}}03"> : tensor<20000xi8> : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK-DAG: %[[MIX:v[0-9]+]] = seaimp.global %mem @"mix" size 24 align 16
// CHECK-DAG: seaimp.mem.fill %mem[%[[MIX]]], dense<[1]> : tensor<1xi8> : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK-DAG: %[[C4:v[0-9]+]] = sea.const 4 : i64
// CHECK-DAG: %[[P4:v[0-9]+]] = sea.ptr.add %[[MIX]], %[[C4]] : !sea.ptr<64>, i64
// CHECK-DAG: seaimp.mem.fill %mem[%[[P4]]], dense<[4, 3, 2, 1, 7, 0]> : tensor<6xi8> : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK-DAG: %[[C12:v[0-9]+]] = sea.const 12 : i64
// CHECK-DAG: %[[P12:v[0-9]+]] = sea.ptr.add %[[MIX]], %[[C12]] : !sea.ptr<64>, i64
// CHECK-DAG: seaimp.mem.fill %mem[%[[P12]]], dense<[2]> : tensor<1xi8> : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK-DAG: %[[C16:v[0-9]+]] = sea.const 16 : i64
// CHECK-DAG: %[[P16:v[0-9]+]] = sea.ptr.add %[[MIX]], %[[C16]] : !sea.ptr<64>, i64
// CHECK-DAG: seaimp.mem.fill %mem[%[[P16]]], dense<[5, 0, 0, 0, 8, 0]> : tensor<6xi8> : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK-DAG: %[[HI:v[0-9]+]] = seaimp.global %mem @"hi" size 4 align 8
// CHECK-DAG: seaimp.mem.fill %mem[%[[HI]]], dense<[255, 128, 1, 127]> : tensor<4xi8> : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK-DAG: %[[HB:v[0-9]+]] = seaimp.global %mem @"hibig" size 300 align 16
// CHECK-DAG: seaimp.mem.fill %mem[%[[HB]]], dense<"0x80FF{{(00)+}}FE"> : tensor<300xi8> : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK-DAG: %[[Z:v[0-9]+]] = seaimp.global %mem @"zero" size 64 align 16
// CHECK-DAG: seaimp.memset %mem[%[[Z]]], %{{v[0-9]+}}, %{{v[0-9]+}} : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK: sea.assert

extern int nd_int(void);
extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define sassert(x)                                                             \
  if (!(x))                                                                    \
  __VERIFIER_error()

struct S {
  char c;
  int x;
  short s;
};
// bytes 1-3 and 10-11 of each element are padding: undef
struct S mix[2] = {{1, 0x01020304, 7}, {2, 5, 8}};
char big[20000] = {1, 2, [19999] = 3};
char hi[4] = {(char)0xff, (char)0x80, 1, 0x7f};
unsigned char hibig[300] = {0x80, 0xff, [299] = 0xfe};
char zero[64];
int tgt;
int *pp[2] = {&tgt, &tgt};

int main(void) {
  int i = nd_int(), k = nd_int();
  __VERIFIER_assume(i >= 0 && i < 20000);
  __VERIFIER_assume(k == 0 || k == 1);
  if (nd_int())
    zero[3] = 1;
  sassert(mix[k].c == k + 1 && mix[k].s == k + 7);
  sassert(mix[k].x == (k ? 5 : 0x01020304));
  sassert(zero[i % 64] == 0 || i % 64 == 3);
  sassert(i < 2 || i == 19999 || big[i] == 0);
  sassert(hi[k] != 1 && hibig[k] != 1);
  sassert(*pp[k] == tgt);
  return 0;
}
