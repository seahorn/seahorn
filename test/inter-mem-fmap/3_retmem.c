// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

#include <stdlib.h>

extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

__attribute__((noinline))
int *create_int(int v) {
  int *p = (int *)malloc(sizeof(int));
  *p = v;
  return p;
}

__attribute__((noinline))
void modify_int(int *p, int v) { *p = v; }

int main() {
  int *p = create_int(100);

  modify_int(p, 42);

  sassert(*p == 42);

  return 0;
}
