// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

// Interesting case 2
// nothing can be copied when calling foo (p1 aliases with p2)
// with no aliasing, p1 could be copied

// do not check satisfiability of this test, it is just meant to test copying
// the memory 
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

extern void sea_dsa_alias(const void *p, ...);

extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

typedef struct Struct {
  struct Struct * x;
  struct Struct * y;
} Struct;
extern Struct *nd_struct();

__attribute__((noinline))
void foo(Struct *p1, Struct *p2) {

  p1->x = NULL;
  p1->y = NULL;

  p2->x = NULL;
  sea_dsa_alias(p2, p2->y);
}

int main() {

  Struct *p1, *p2;
  p1 = nd_struct();
  p2 = nd_struct();

  sea_dsa_alias(p1, p2);

  foo(p1, p2);

  sassert(p1->x == NULL);

  return 0;
}
