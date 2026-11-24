// A single failure site keeps its location: MixedSemantics turns the
// __VERIFIER_error call into a branch to the shared error block, and when
// every branch into that block has one location, the block's seahorn.fail
// and ret take it too. Otherwise -O3 folds the only branch into its
// predecessor and the exported sea.assert has no location (an assert-at
// would then name the last located op, inside the inlined callee).
// RUN: %sea yama -y sea-mlir-export --bound=1 -m64 -g --horn-sea-mlir-out=%t.mlir "%s"
// RUN: filecheck %s < %t.mlir
// CHECK: sea.assert {{.*}} loc("{{.*}}sea_mlir_error_loc.c":27:5)

extern int nd_int(void);
extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);

static int step(int x) {
  int y = x * 3;
  if (y > 7)
    return y + 1;
  return y - 1;
}

int main(void) {
  int a = nd_int();
  __VERIFIER_assume(a > 0 && a < 10);
  int k = step(a);
  if (k > 20)
    __VERIFIER_error();
  return 0;
}
