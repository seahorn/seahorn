// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$


#include <stdlib.h>

extern void sea_dsa_alias(const void *p, ...);
extern int nd_int();
extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

typedef struct Struct {
  struct Struct *x;
  struct Struct *y;
} Struct;

extern Struct *nd_struct();

int main() {
  Struct * s1 = nd_struct();
  Struct * s2 = nd_struct();

  s1->x = s2;
  s2->x = 0;
  s1->y = 0;

  s1->x->y = 0; // accessing s2 through s1

  sassert(s1->y==0);

  return 0;
}
