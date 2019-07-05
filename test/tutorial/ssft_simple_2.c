// RUN: %shorntest %t-harness.ll %t-debug %s --max-depth=9 | OutputCheck %s --check-prefix=XFAIL_UNKNOWN
// RUN: %shorntest %t-harness0.ll %t-debug0 %s -O0 --max-depth=9 | OutputCheck %s
// RUN: %shorntest %t-harness1.ll %t-debug1 %s -O1 --max-depth=9 | OutputCheck %s --check-prefix=XFAIL_UNKNOWN
// RUN: %shorntest %t-harness2.ll %t-debug2 %s -O2 --max-depth=9 | OutputCheck %s --check-prefix=XFAIL_UNKNOWN
// RUN: %shorntest %t-harness3.ll %t-debug3 %s -O3 --max-depth=9 | OutputCheck %s --check-prefix=XFAIL_UNKNOWN
// CHECK: ^unsat$
// XFAIL_UNKNOWN: ^unknown$

int unknown(void);

extern void __VERIFIER_assume(int);
extern void __VERIFIER_error(void);
void assert(int v) {
  if (!v)
    __VERIFIER_error();
}

#define static_assert assert

int main(void) {
  int k = 1;
  int i = 1;
  int j;
  int n = unknown();
  while (i < n) {
    j = 0;
    while (j < i) {
      k += (i - j);
      j++;
    }
    i++;
  }
  static_assert(k >= n);
  return 0;
}
