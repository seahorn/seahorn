// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

#include <stdlib.h>

extern void sea_dsa_alias(const void *p, ...);
extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

typedef struct LElem {
  int data;
  struct LElem *next;
} LElem;


__attribute__((noinline))
void add_to_end(LElem *e, int v) {
  LElem *newe = (LElem *)malloc(sizeof(LElem));

  e->next = newe;
  e->data = v;
  newe->next = NULL;
}

__attribute__((noinline))
void do_nothing2(LElem *e) {}

__attribute__((noinline))
void do_nothing(LElem * e) { do_nothing2(e); }

int main() {
  LElem e1, e2;
  sea_dsa_alias(&e1,&e2);

  add_to_end(&e1, 0);
  /* add_to_end(&e2, 37); */

  assume(&e1 + sizeof(struct LElem) < &e2);
  /* assume(&e1.next + sizeof(struct LElem) < &e2.next); */

  //  sea_dsa_alias(&e1.next,&e2.next);
  do_nothing(&e2);

  sassert(e1.next->next == 0);

  return 0;
}
