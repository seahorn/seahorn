// sea-dsa's shadow-memory optimizer trusts the front end's TBAA metadata
// (--horn-shadow-mem-use-tbaa, on by default): a load skips a store made
// through another type. set_len writes B's length through A, a
// strict-aliasing violation, so with TBAA the load of v[j].len reads the
// memory version from before set_len's store; the reach of the error is then
// unsat although the program reaches it. The export reports the reliance (a
// warning and a header comment); without TBAA the load reads the latest
// version and nothing is reported. SeaHorn's own engines count it as a stat
// only.
// RUN: %sea yama -y sea-mlir-export -O0 --bound=1 -m64 -g --horn-sea-mlir-out=%t.mlir "%s" 2>&1 | filecheck %s --check-prefix=WARN
// RUN: filecheck %s --check-prefix=STALE < %t.mlir
// RUN: %sea yama -y sea-mlir-export -O0 --bound=1 -m64 -g --horn-shadow-mem-use-tbaa=false --horn-sea-mlir-out=%t.off.mlir "%s" 2>&1 | filecheck %s --check-prefix=OFF
// RUN: filecheck %s --check-prefix=LATEST < %t.off.mlir
// RUN: %sea bpf -O0 -m64 --horn-stats "%s" 2>&1 | filecheck %s --check-prefix=STAT
// WARN: Warning: sea-mlir export: TBAA moved 1 shadow-memory use past stores; to check whether a result depends on it, re-export with --horn-shadow-mem-use-tbaa=false
// WARN: sea-mlir-export: wrote
// STALE: // sea-mlir-export: TBAA moved 1 shadow-memory use past stores
// STALE: %[[S:v[0-9]+]] = sea.store %[[M:v[0-9]+]][{{.*}} loc(callsite(
// STALE: sea.load %[[M]][
// OFF-NOT: TBAA moved
// OFF: sea-mlir-export: wrote
// LATEST-NOT: TBAA moved
// LATEST: %[[S:v[0-9]+]] = sea.store %{{v[0-9]+}}[{{.*}} loc(callsite(
// LATEST: sea.load %[[S]][
// STAT-NOT: Warning: {{.*}}TBAA
// STAT: {{^}}unsat{{$}}
// STAT: BRUNCH_STAT shadow.mem.tbaa-moved-uses 1
// STAT: BRUNCH_STAT shadow.mem.tbaa-noalias-skips 1

extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
extern long nd_i64(void);
struct A {
  char *p;
  long len;
};
struct B {
  char *p;
  long len;
};
static void set_len(struct A *a) { a->len = 1; } // store, TBAA tag A::len
int main(void) {
  struct B *v = (struct B *)__builtin_malloc(2 * sizeof(struct B));
  long i = nd_i64();
  __VERIFIER_assume(i == 1);
  v[0].len = 0;
  v[1].len = 0;
  set_len((struct A *)&v[i]);
  long j = nd_i64();
  __VERIFIER_assume(j == 1);
  __VERIFIER_assume(v[j].len == 1); // load, TBAA tag B::len
  __VERIFIER_error();               // reached natively
  return 0;
}
