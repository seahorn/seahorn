// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

#include <stdlib.h>
#include <stdio.h>

extern int nd_int(void);
extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

int * g;

__attribute__((noinline))
void modify_int(int *p, int *q, int v) {
  *p = v;
  *q = v;
}

int main(int argc, char ** argv) {
  g = (int *)malloc(2 * sizeof(int));
  int *q = (int *)malloc(2 * sizeof(int));
  int *r = g;
  r[1] = 42;
  int count = 0;

  modify_int(g, q, 42);

  sassert(*g == 42 && *q == 42 && g[1] == 42);

  return 0;
}
