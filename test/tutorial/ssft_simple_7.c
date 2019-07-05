// RUN: %shorntest %t-harness.ll %t-debug %s --max-depth=15 | OutputCheck %s
// RUN: %shorntest %t-harness0.ll %t-debug0 %s -O0 --max-depth=15 | OutputCheck %s
// RUN: %shorntest %t-harness1.ll %t-debug1 %s -O1 --max-depth=15 | OutputCheck %s
// RUN: %shorntest %t-harness2.ll %t-debug2 %s -O2 --max-depth=15 | OutputCheck %s
// RUN: %shorntest %t-harness3.ll %t-debug3 %s -O3 --max-depth=15 | OutputCheck %s
// CHECK: ^unsat$

int unknown(void);

extern void __VERIFIER_assume(int);
extern void __VERIFIER_error(void);
void assert(int v) {
  if (!v)
    __VERIFIER_error();
}

#define static_assert assert

/*
 * InvGen, CAV'09 paper, fig 2
 */

int main(void) {
  int x = 0;
  int n = unknown();
  while (x < n) {
    x++;
  }
  if (n > 0)
    static_assert(x == n);
}
