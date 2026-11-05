// sea-mlir export locations: the source path, line and column of each op;
// an op inlined from a callee is callsite(<callee position> at <call
// position>); a global gets its declaration's line (column 0); no names
// SeaHorn generated (_N, sm<N>, shadow.mem.<N>). The source is compiled by
// path, so its location is the path (relative to the compilation directory
// when it is under it).
// RUN: %sea yama -y sea-mlir-export --bound=1 -m64 -g --horn-sea-mlir-out=%t.mlir "%s"
// RUN: filecheck %s < %t.mlir
// RUN: filecheck %s --check-prefix=NONAME < %t.mlir
// RUN: filecheck %s --check-prefix=NOLINK < %t.mlir
// Debugging mode: --horn-sea-mlir-ll-out writes the exported module and
// links every op to its instruction there (fused<"llvm @f %bb #i">); an op
// without a source position gets its position in the .mlir.
// RUN: %sea yama -y sea-mlir-export --bound=1 -m64 -g --horn-sea-mlir-out=%t.ll.mlir --horn-sea-mlir-ll-out=%t.ll "%s"
// RUN: filecheck %s --check-prefix=LINK < %t.ll.mlir
// RUN: filecheck %s --check-prefix=LL < %t.ll
// RUN: grep -E '^  [^ ]' %t.ll.mlir | not grep -v 'fused<"llvm @'
// CHECK: sea.global @"tab" {{.*}} loc("{{.*}}sea_mlir_locations.c":39:0)
// CHECK: sea.and {{.*}} loc(callsite("{{.*}}sea_mlir_locations.c":42:19 at "{{.*}}sea_mlir_locations.c":49:11))
// CHECK: sea.print.scope "step" loc(callsite("{{.*}}sea_mlir_locations.c":43:3 at "{{.*}}sea_mlir_locations.c":49:11))
// CHECK: sea.print "p" {{.*}} loc(callsite("{{.*}}sea_mlir_locations.c":43:3 at "{{.*}}sea_mlir_locations.c":49:11))
// NONAME-NOT: loc("_{{[0-9]+}}
// NONAME-NOT: loc("sm{{[0-9]*}}
// NONAME-NOT: loc("shadow.mem
// NOLINK-NOT: fused<
// LINK: sea.global @"tab" {{.*}} loc(fused<"llvm @tab">["{{.*}}sea_mlir_locations.c":39:0])
// LINK: sea.nondet "nd_int" {{.*}} loc(fused<"llvm @main %{{[^ ]+}} #{{[0-9]+}}">["{{.*}}sea_mlir_locations.c":
// LINK: sea.print "p" {{.*}} loc(fused<"llvm @main %{{[^ ]+}} #{{[0-9]+}}">[callsite(
// LINK: sea.assert {{.*}} loc(fused<"llvm @main %{{[^ ]+}} #{{[0-9]+}}">["{{.*}}.ll.mlir":[[#]]:3])
// LL: @tab = {{.*}}global [4 x i32]
// LL: define {{.*}}@main(
// LL: call i32 @nd_int()

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
