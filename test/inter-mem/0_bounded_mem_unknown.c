// RUN: sea pf -O0 --dsa=sea-cs --max-depth=10 --horn-shadow-mem-optimize=false %s
// CHECK: ^unknown$
// XFAIL: *

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>

extern void sea_dsa_alias(const void *p, ...);
extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error (), 0))

typedef struct Struct {
  int x;
  int y;
} Struct;

void modify_x(Struct *s, int v) {
  s->x = v;
}

void modify_y(Struct *s, int v) {
  s->y = v;
}

int read_x(Struct *s) {
  return s->x;
}

int read_y(Struct *s) {
  return s->y;
}

int main() {
  Struct* p = (Struct*) malloc(sizeof(Struct));
  Struct* q = (Struct*) malloc(sizeof(Struct));

  // Some modeling of malloc: p is disjoint from q
  assume(p + sizeof(Struct) < q);

  p->x = 10;
  p->y = 0;

  q->x = 20;
  q->y = 0;

  // We force the pointer analysis to believe that p,q might alias
  sea_dsa_alias(p,q);

  /**
   * EXPECTED: SAFE (unsat)
   * Spacer cannot converge. The proof requires that q->y is 0.

   * The problem is that modify_x's summary cannot mention q since
   * it's not part of the available language.  As a result, modify_x
   * needs to produce a summary in which the array associated to p and
   * q (since they alias), all array elements except the one
   * corresponding to p->x are unmodified. This requires currently an
   * infinite enumeration.
   *
   **/
  modify_x(p, 30);
  sassert(read_y(q) == 0);
  return 0;
}
