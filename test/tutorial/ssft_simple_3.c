// RUN: %shorntest %t-harness.ll %t-debug %s --max-depth=15 --enable-indvar | OutputCheck %s
// RUN: %shorntest %t-harness0.ll %t-debug0 %s --max-depth=15 -O0 --enable-indvar | OutputCheck %s --check-prefix=XFAIL_UNKNOWN
// RUN: %shorntest %t-harness1.ll %t-debug1 %s --max-depth=15 -O1 --enable-indvar | OutputCheck %s
// RUN: %shorntest %t-harness2.ll %t-debug2 %s --max-depth=15 -O2 --enable-indvar | OutputCheck %s
// RUN: %shorntest %t-harness3.ll %t-debug3 %s --max-depth=15 -O3 --enable-indvar | OutputCheck %s
// RUN: %shorntest %t-harness-.ll %t-debug- %s --max-depth=15 | OutputCheck %s --check-prefix=XFAIL_NOT_UNKNOWN
// CHECK: ^unsat$
// XFAIL_UNKNOWN: ^unknown$
// XFAIL_NOT_UNKNOWN: ^unsat$

/* requires --enable-indvar */
int unknown(void);

extern void __VERIFIER_assume(int);
extern void __VERIFIER_error(void);
void assert(int v) {
  if (!v)
    __VERIFIER_error();
}
#define assume __VERIFIER_assume
#define static_assert assert

/*
 * Adapted from ex17.c in NECLA test suite
 */

#ifndef BND
#define BND 100
#endif

int main(void) {
  int b;
  int j = 0;
  int flag = unknown();

  for (b = 0; b < BND; ++b) {
    if (flag)
      j = j + 1;
  }

  if (flag)
    static_assert(j == BND);

  return 0;
}
