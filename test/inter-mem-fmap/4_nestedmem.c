// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

#include <stdlib.h>

extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

typedef struct LElem {
  int data;
  struct LElem *next;
} LElem;

__attribute__((noinline))
void add_to_end(LElem *e) {
  LElem *newe = (LElem * )malloc(sizeof(LElem));

  e->next = newe;
  newe->next = 0;
}

int main() {
  LElem e1;

  add_to_end(&e1);

  sassert(e1.next->next == 0);

  return 0;
}
