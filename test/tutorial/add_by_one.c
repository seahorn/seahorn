// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// RUN: %shorntest %t-harness0.ll %t-debug0 %s -O0 | OutputCheck %s
// RUN: %shorntest %t-harness1.ll %t-debug1 %s -O1 | OutputCheck %s
// RUN: %shorntest %t-harness2.ll %t-debug2 %s -O2 | OutputCheck %s
// RUN: %shorntest %t-harness3.ll %t-debug3 %s -O3 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

extern int nd(void);

int main(void) {
  int x = nd();
  int y = nd();
  assume(y >= 0);

  int r;
  r = x;
  int c = y;
  while (c > 0) {
    r = r + 1;
    c = c - 1;
  }
  printf("x=%d, y=%d, r=%d\n", x, y, r);
  sassert(r == x + y);
  return 0;
}
