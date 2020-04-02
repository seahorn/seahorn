// RUN: sea pf -O0 --dsa=sea-cs --horn-inter-proc-mem --horn-shadow-mem-optimize=false %s
// CHECK: ^unsat$

/*
  This example is similar to mem-vcgen-3.c but here we want to show that if the
  structure contains pointers, and we know that the amount of modified memory is
  finite, we have to recursively copy all the
  memory positions that could be modified.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>

extern void sea_dsa_alias(const void *p, ...);
extern int8_t* nd_int8_ptr();
extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error (), 0))

typedef struct Struct2 {
  int r;
  int s;
} Struct2;

typedef struct Struct1 {
  int x;
  int y;
  Struct2 * t;
} Struct1;

void modify_x(Struct1 *s, int v) {
  s->x = v;
}

void modify_y(Struct1 *s, int v) {
  s->y = v;
}

int read_x(Struct1 *s) {
  return s->x;
}

int read_y(Struct1 *s) {
  return s->y;
}

int read_t_s(Struct1 *s) {
  return s->t->s;
}

void modify_r(Struct2 *s, int v) {
  s->r = v;
}

void modify_t_r(Struct1 *s, int v) {
  modify_r(s->t,v);
}

int main() {

  Struct1* p = (Struct1*) malloc(sizeof(Struct1));
  p->t = (Struct2*) malloc(sizeof(Struct2));
  Struct1* q = (Struct1*) malloc(sizeof(Struct1));
  q->t = (Struct2*) malloc(sizeof(Struct2));

  // We force the pointer analysis to believe that p,q might alias
  sea_dsa_alias(p,q);

  // Some modeling of malloc: p is disjoint from q
  assume(p + sizeof(Struct1) < p->t);
  assume(p->t + sizeof(Struct2) < q);
  assume(q + sizeof(Struct1) < q->t);

  p->x = 10;
  p->y = 1;

  q->x = 20;
  q->y = 0;
  q->t->s = 42;

  // we force the pointer analysis to believe that p,q might alias
  sea_dsa_alias(p,q);
  modify_t_r(p, 30);
  sassert(read_t_s(q) == 42);

  return 0;
}
