// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

#include <stdlib.h>

extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

typedef struct LElem {
  struct LElem *n1;
  struct LElem *n2;
} LElem;


__attribute__((noinline))
void add_to_end(LElem *e) {
  LElem *n1 = (LElem * )malloc(sizeof(LElem));
  LElem *n2 = (LElem * )malloc(sizeof(LElem));

  e->n1 = n1;
  e->n1 = n2;

  e->n1->n1 = e->n1->n2;

  e->n1->n1 = 0;

}

int main() {
  LElem e1;

  add_to_end(&e1);

  sassert(e1.n1->n1 == 0);
  return 0;
}
