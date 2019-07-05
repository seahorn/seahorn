// RUN: %shorntest %t-harness.ll %t-debug %s --max-depth=15 | OutputCheck %s --check-prefix=XFAIL_UNKNOWN
// RUN: %shorntest %t-harness0.ll %t-debug0 %s -O0 --max-depth=15 | OutputCheck %s
// RUN: %shorntest %t-harness1.ll %t-debug1 %s -O1 --max-depth=15 | OutputCheck %s --check-prefix=XFAIL_UNKNOWN
// RUN: %shorntest %t-harness2.ll %t-debug2 %s -O2 --max-depth=15 | OutputCheck %s --check-prefix=XFAIL_UNKNOWN
// RUN: %shorntest %t-harness3.ll %t-debug3 %s -O3 --max-depth=15 | OutputCheck %s --check-prefix=XFAIL_UNKNOWN
// CHECK: ^unsat$
// XFAIL_UNKNOWN: ^unknown$

int unknown1(void);

/*
 * from Invgen test suite
 */

extern void __VERIFIER_assume(int);
extern void __VERIFIER_error(void);
void assert(int v) {
  if (!v)
    __VERIFIER_error();
}

#define assume __VERIFIER_assume
#define static_assert assert

int main(void) {

  int n, k, j;

  n = unknown1();
  assume(n > 0);

  k = unknown1();
  assume(k > n);
  j = 0;
  while (j < n) {
    j++;
    k--;
  }
  static_assert(k >= 0);
  return 0;
}
