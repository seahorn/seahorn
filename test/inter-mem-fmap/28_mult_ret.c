// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

#include <stdlib.h>

extern unsigned nd();
extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error (), 0))

#define INT_MAX 30

typedef struct baz{
  int data;
} baz;

__attribute__((noinline))
baz *foo(baz *n) {
  baz  *p;
  if (n->data == INT_MAX) {
    p = (baz *)malloc(sizeof(baz));
  } else {
    p = n;
  }
  p->data = 5;
  if (n->data == INT_MAX)
    return p;
  else
    return n;
}
void bar(baz* q, baz *r);
int main() {
  baz *q, *r;
  baz *objs[10];
  for (int i = 0; i < 10; i++) {
    objs[i] = (baz *)malloc(sizeof(baz));
  }
  unsigned j = nd();
  assume(0 <= j && j < 10);
  q = objs[j];
  r = foo(q);
  bar(q, r);

  sassert(r->data == 5);
  return 0;
}
