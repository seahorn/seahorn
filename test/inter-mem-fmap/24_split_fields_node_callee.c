// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

// TODO: this is crashing right now

#include <stdlib.h>

extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

typedef struct Struct {
  int x;
  int y;
} Point;


__attribute__((noinline))
void modify_int(int *x, int *y, int v) {
  *x = v;
  *y = v;
}

__attribute__((noinline))
void modify_point(Point *p, int v) {
  modify_int(&p->x, &p->y, v);
}

int main() {

  Point * p =(Point *)malloc(sizeof(Point));

  // p -> *p // defk(p)
  // q -> *q // defk(q)

  // x = p,  // x -> *p // defk(x)
  modify_point(p, 42);

  sassert(p->x == 42);

  return 0;
}
