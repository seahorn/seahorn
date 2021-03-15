// RUN: %sea smt %s --step=small -o %t.smt2
// RUN: %z3 %t.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

extern int nd1();
extern int nd2();
extern int nd3();
extern int nd4();
extern int nd5();
extern int nd6();

// Loop invariant.
extern bool infer(int a, int b);
bool PARTIAL_FN inv1(int x, int y) { return infer(x, y); }
bool PARTIAL_FN inv2(int x, int n) { return infer(x, n); }

// Test.
int main(void) {
  // See 03_loop.unsat.c.

  int x1 = 0;
  int y1 = 0;
  int n1 = nd1();
  assume(n1 > 0);

  if (nd2()) __VERIFIER_assert(inv1(x1, y1));
  else __VERIFIER_assert(inv2(x1, n1));

  int x2 = nd3();
  int y2 = nd4();
  int n2 = nd5();
  assume(inv1(x2, y2));
  assume(inv2(x2, n2));
  if (x2 < n2) {
    x2 += 1; y2 += 1;
    if (nd6()) __VERIFIER_assert(inv1(x2, y2));
    else __VERIFIER_assert(inv2(x2, n2));
    assume(0);
  }

  sassert(y2 == n2);
}
