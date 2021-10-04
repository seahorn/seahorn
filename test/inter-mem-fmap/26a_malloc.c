// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^sat$

// TODO: why sat?

#include <stdlib.h>

extern int nd();
extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error (), 0))

#define INT_MAX 30
#define NOBJS 5

__attribute__((noinline))
int *foo(int *n) {
  int *p;
  if (*n == INT_MAX)
    p = (int *)malloc(sizeof(int));
  else
    p = n;

  *p = 5;
  return p;
}

void bar(int* q, int *r);

int main() {
  int *q, *r;
  int *objs[NOBJS];
  for (int i = 0; i < NOBJS; i++){
    objs[i] = (int *)malloc(sizeof(int));
    *objs[i] = 42;
  }

  int j = nd();
  assume(0 <= j && j < NOBJS);
  q = objs[j];
  r = foo(q);
  // bar(q, r);

  int k = nd();
  assume(0 <= k && k < NOBJS && k != j);
  sassert(*objs[k] == 42);
  return 0;
}
