// RUN: %sea pf --max-depth=20 "%s" 2>&1 | OutputCheck %s
// RUN: %sea pf --enable-indvar %s 2>&1 | OutputCheck %s
// CHECK: ^unsat$

// Source: Thomas A. Henzinger, Thibaud Hottelier, Laura Kovacs: "Valigator:
// A verification Tool with Bound and Invariant Generation", LPAR 2008

#include "seahorn/seahorn.h"

extern int nd(void);

int main() {
  int a = nd();
  int b = nd();
  int res, cnt;
  if (!(a <= 1000000))
    return 0;
  if (!(0 <= b && b <= 1000000))
    return 0;
  res = a;
  cnt = b;
  while (cnt > 0) {
    cnt = cnt - 1;
    res = res + 1;
  }
  sassert(res == a + b);
  return 0;
}
