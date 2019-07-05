// RUN: %shorntest %t-harness.ll %t-debug %s --max-depth=15 | OutputCheck %s
// RUN: %shorntest %t-harness0.ll %t-debug0 %s -O0 --max-depth=15 | OutputCheck %s
// RUN: %shorntest %t-harness1.ll %t-debug1 %s -O1 --max-depth=15 | OutputCheck %s
// RUN: %shorntest %t-harness2.ll %t-debug2 %s -O2 --max-depth=15 | OutputCheck %s
// RUN: %shorntest %t-harness3.ll %t-debug3 %s -O3 --max-depth=15 | OutputCheck %s
// CHECK: ^unsat$

int unknown(void);
int unknown1(void);

/*
 * "nest-if8" from InvGen benchmark suite
 */

extern void __VERIFIER_error(void);
void assert(int v) {
  if (!v)
    __VERIFIER_error();
}

#define static_assert assert

int main(void) {
  int i, j, k, n, m;
  i = unknown();
  j = unknown();
  n = unknown();
  m = unknown();

  if (m + 1 < n)
    ;
  else
    return 0;

  for (i = 0; i < n; i += 4) {
    for (j = i; j < m;) {
      if (unknown1()) {
        j++;
        k = 0;
        while (k < j) {
          k++;
        }
      } else {
        static_assert(n + j + 5 > i);
        j += 2;
      }
    }
  }
}
