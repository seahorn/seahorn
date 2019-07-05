// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// RUN: %shorntest %t-harness0.ll %t-debug0 %s -O0 | OutputCheck %s
// RUN: %shorntest %t-harness1.ll %t-debug1 %s -O1 | OutputCheck %s
// RUN: %shorntest %t-harness2.ll %t-debug2 %s -O2 | OutputCheck %s
// RUN: %shorntest %t-harness3.ll %t-debug3 %s -O3 | OutputCheck %s
// CHECK: ^sat$
// CHECK-NEXT: ^\[sea\] __VERIFIER_error was executed$

#include <seahorn/seahorn.h>

extern int unknown1(void);

int main(void) {
  int x = 1;
  int y = 1;
  while (unknown1()) {
    int t1 = x;
    int t2 = y;
    x = t1 + t2;
    y = t1 + t2;
  }
  sassert(y < 1);
  return 0;
}
