// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^sat$


struct a {
  void *b;
} c();
void __VERIFIER_error();
static void d() { __VERIFIER_error(); }
__attribute__((noinline)) void e(struct a *g) { c(g->b); }
void f() { d; }
