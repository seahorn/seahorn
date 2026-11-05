// sea-mlir export locations: the source path, line and column of each op;
// an op inlined from a callee is callsite(<callee position> at <call
// position>); a global gets its declaration's line (column 0); no names
// SeaHorn generated (_N, sm<N>, shadow.mem.<N>). The source is compiled by
// path, so its location is the path (relative to the compilation directory
// when it is under it).
// RUN: %sea yama -y sea-mlir-export --bound=1 -m64 -g --horn-sea-mlir-out=%t.mlir "%s"
// RUN: filecheck %s < %t.mlir
// RUN: filecheck %s --check-prefix=NONAME < %t.mlir
// CHECK: sea.global @"tab" {{.*}} loc("{{.*}}sea_mlir_locations.c":23:0)
// CHECK: sea.and {{.*}} loc(callsite("{{.*}}sea_mlir_locations.c":26:19 at "{{.*}}sea_mlir_locations.c":33:11))
// CHECK: sea.print.scope "step" loc(callsite("{{.*}}sea_mlir_locations.c":27:3 at "{{.*}}sea_mlir_locations.c":33:11))
// CHECK: sea.print "p" {{.*}} loc(callsite("{{.*}}sea_mlir_locations.c":27:3 at "{{.*}}sea_mlir_locations.c":33:11))
// NONAME-NOT: loc("_{{[0-9]+}}
// NONAME-NOT: loc("sm{{[0-9]*}}
// NONAME-NOT: loc("shadow.mem

extern int nd_int(void);
extern void __VERIFIER_error(void);
extern __declspec(noalias) void sea_printf(const char *format, ...);
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

int tab[4] = {1, 2, 3, 4};

static int step(int x) {
  int *p = &tab[x & 3];
  sea_printf("step: x=%d p=%p", x, p);
  return x + *p;
}

int main(void) {
  int x = nd_int();
  int y = step(x);
  sassert(y != 11);
  return 0;
}
