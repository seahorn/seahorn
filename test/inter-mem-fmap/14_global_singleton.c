// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

extern void sea_dsa_alias(const void *p, ...);
extern int * nd_int();
extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

int * ig;

int main() {

  ig = nd_int();

  *ig = 0;

  sassert(*ig == 0);

  return 0;
}
