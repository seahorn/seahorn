// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

extern int nd(void);

int main(void)
{
  int x = nd();
  int y = nd();
  assume (y>=0);

  int r;
  r = x;
  int c = y;
  while (c > 0) {
    r = r + 1;
    c = c - 1;
  }
  printf ("x=%d, y=%d, r=%d\n", x, y, r);
  sassert (r == x + y);
  return 0;
}
