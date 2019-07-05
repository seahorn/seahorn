// RUN: %shorntest %t-harness.ll %t-debug %s --max-depth=15 | OutputCheck %s
// RUN: %shorntest %t-harness0.ll %t-debug0 %s -O0 --max-depth=15 | OutputCheck %s
// RUN: %shorntest %t-harness1.ll %t-debug1 %s -O1 --max-depth=15 | OutputCheck %s
// RUN: %shorntest %t-harness2.ll %t-debug2 %s -O2 --max-depth=15 | OutputCheck %s
// RUN: %shorntest %t-harness3.ll %t-debug3 %s -O3 --max-depth=15 | OutputCheck %s
// CHECK: ^unsat$

int unknown(void);
int unknown1(void);

extern void __VERIFIER_assume(int);
extern void __VERIFIER_error(void);
void assert(int v) {
  if (!v)
    __VERIFIER_error();
}

#define static_assert assert
#define assume __VERIFIER_assume

int main(void) {
  int i = unknown();
  int y = unknown();
  int x = unknown();
  int k = unknown();
  int j = unknown();
  int n = unknown();
  assume((x + y) == k);
  int m = 0;
  j = 0;
  while (j < n) {
    if (j == i) {
      x++;
      y--;
    } else {
      y++;
      x--;
    }
    if (unknown1())
      m = j;
    j++;
  }
  static_assert((x + y) == k);
  if (n > 0) {
    static_assert(0 <= m);
    static_assert(m < n);
  }
  return 0;
}
