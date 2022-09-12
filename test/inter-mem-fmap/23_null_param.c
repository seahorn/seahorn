// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

#include <stdlib.h>

extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

// (int, int, int, fmap(defk(x)), fmap(defk(x)), fmap(defk(y)), fmap(defk(y)))
__attribute__((noinline))
void modify_int(int *x, int *y, int v) {
  *x = v;
  *y = v;
}

int main() {

  int *p = (int *)malloc(2*sizeof(int));
  int *q = (int *)malloc(2 * sizeof(int));

  // p -> *p // defk(p)
  // q -> *q // defk(q)

  // x = p,  // x -> *p // defk(x)
  modify_int(p, 0, 42);

  sassert(*p == 42);

  return 0;
}
