// The sea-mlir export with memory SSA erased (--horn-sea-mlir-mem-ssa=erase):
// one seaimp region variable "mem" at the start of the entry block instead
// of a sea.mem.nondet per shadow-memory region; every memory instruction is
// the seaimp region op on it, with no memory versions, no `inplace` and no
// memory block arguments (a loop exit merges memory in the default form,
// KEEP); allocation names the region (alloca, malloc, global).
// RUN: %sea yama -y sea-mlir-export -O0 --bound=4 -m64 --horn-sea-mlir-out=%t.keep.mlir "%s" 2>&1 | filecheck %s --check-prefix=LOG
// RUN: filecheck %s --check-prefix=KEEP < %t.keep.mlir
// RUN: %sea yama -y sea-mlir-export -O0 --bound=4 -m64 --horn-sea-mlir-mem-ssa=erase --horn-sea-mlir-out=%t.mlir "%s" 2>&1 | filecheck %s --check-prefix=LOG
// RUN: filecheck %s < %t.mlir
// RUN: not grep -E 'sea\.mem\.nondet|inplace|: !sea\.mem<|sea\.(load|store|alloca|malloc|global|memset|memmove|mem\.is_modified|mem\.reset_modified) ' %t.mlir
// LOG: sea-mlir-export: wrote
// KEEP: sea.mem.nondet "region.
// KEEP: ^bb{{[0-9]+}}(%{{v[0-9]+}} : !sea.mem<!sea.ptr<64>, i8>):
// CHECK: sea.program @"main" {
// CHECK-NEXT: ^bb0:
// CHECK-NEXT: %mem = seaimp.var "mem" [0] : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK: = seaimp.global %mem @"g" size 16 align 16 : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>> -> !sea.ptr<64>
// CHECK-NEXT: seaimp.mem.fill %mem[%{{v[0-9]+}}], dense<[1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0]> : tensor<16xi8> : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK: %[[A:v[0-9]+]] = seaimp.alloca %mem, %{{v[0-9]+}} align 16 [{{[0-9]+}}] : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>, i64 -> !sea.ptr<64>
// CHECK: = seaimp.malloc %mem, %{{v[0-9]+}} align 16 [{{[0-9]+}}] : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>, i64 -> !sea.ptr<64>
// straight-line: a load of g, a store to a[0]
// CHECK: %[[X:v[0-9]+]] = seaimp.load %mem[%{{v[0-9]+}}] align 4 : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>> -> i32
// CHECK-NEXT: seaimp.store %mem[%[[A]]], %[[X]] align 16 : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>, i32
// the unrolled loop: stores, and only i32 block arguments
// CHECK: ^bb{{[0-9]+}}(%{{v[0-9]+}} : i32):
// CHECK: seaimp.store %mem[%{{v[0-9]+}}], %{{v[0-9]+}} align 4 : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>, i32
// CHECK: seaimp.memset %mem[%{{v[0-9]+}}], %{{v[0-9]+}}, %{{v[0-9]+}} align 16 : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK: seaimp.memmove %mem[%{{v[0-9]+}}], %mem[%[[A]]], %{{v[0-9]+}} align 16 src_align 16 : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK: seaimp.memhavoc %mem[%{{v[0-9]+}}], %{{v[0-9]+}} [{{[^]]*}}] : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// calloc: the allocation, then the zero fill of the region
// CHECK: %[[Z:v[0-9]+]] = seaimp.malloc %mem, %{{v[0-9]+}} align 16 [{{[0-9]+}}] : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>, i64 -> !sea.ptr<64>
// CHECK: seaimp.memset %mem[%[[Z]]], %{{v[0-9]+}}, %{{v[0-9]+}} : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK: sea.tracking_on
// CHECK-NEXT: seaimp.reset_modified %mem[%{{v[0-9]+}}] : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK-NEXT: = seaimp.is_modified %mem[%{{v[0-9]+}}] : !seaimp.var<!sea.mem<!sea.ptr<64>, i8>>
// CHECK: sea.tracking_off
// CHECK: sea.assert

#include "seahorn/seahorn.h"
#include <string.h>

extern int nd_int(void);
extern void *malloc(unsigned long);
extern void *calloc(unsigned long, unsigned long);
extern void memhavoc(char *, unsigned long);
extern void sea_reset_modified(char *);
extern bool sea_is_modified(char *);
extern void sea_tracking_on(void);
extern void sea_tracking_off(void);

int g[4] = {1, 2, 3, 4};
int *keep;

int main(void) {
  int a[8];
  int n = nd_int();
  assume(n > 0 && n <= 4);
  int *h = (int *)malloc(4 * sizeof(int));
  keep = (int *)malloc(sizeof(int));
  a[0] = g[n - 1];
  for (int i = 0; i < n; i++)
    a[i + 1] = i;
  memset(h, 0, 4 * sizeof(int));
  memcpy(h, a, n * sizeof(int));
  char hv[4];
  memhavoc(hv, 4);
  int *z = (int *)calloc(2, sizeof(int));
  sassert(z[1] == 0);
  sea_tracking_on();
  sea_reset_modified((char *)h);
  int x = h[0];
  sassert(!sea_is_modified((char *)h));
  sea_tracking_off();
  sassert(x == g[n - 1]);
  return 0;
}
