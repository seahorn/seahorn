// RUN: %sea pf "%s"  2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"
extern int unknown1();

int main() {
  int x = 1;
  int y = 1;
  while (unknown1()) {
    int t1 = x;
    int t2 = y;
    x = t1 + t2;
    y = t1 + t2;
  }
  sassert(y >= 1);
}
