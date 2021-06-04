// RUN: %sea smt %s --step=small -o %t.sm.smt2
// RUN: %z3 %t.sm.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=small --inline -o %t.sm.inline.smt2
// RUN: %z3 %t.sm.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=large -o %t.lg.smt2
// RUN: %z3 %t.lg.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=large --inline -o %t.lg.inline.smt2
// RUN: %z3 %t.lg.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// CHECK: ^sat$

#include "seahorn/seahorn.h"

extern int nd1();
extern int nd2();
extern int nd3();
extern int nd4();
extern int nd5();
extern int nd6();

// Loop invariant.
extern bool infer(int a, int b);
bool PARTIAL_FN inv1(int x, int n) { return infer(x, n); }
bool PARTIAL_FN inv2(int y, int n) { return infer(y, n); }

// Test.
int main(void) {
  // See 03_loop.unsat.c.

  int x1 = 0;
  int y1 = 0;
  int n1 = nd1();
  assume(n1 > 0);

  if (nd2()) __VERIFIER_assert(inv1(x1, n1));
  else __VERIFIER_assert(inv2(y1, n1));

  int x2 = nd2();
  int y2 = nd3();
  int n2 = nd4();
  assume(inv1(x2, n2));
  assume(inv2(y2, n2));
  if (x2 < n2) {
    x2 += 1; y2 += 1;
    if (nd6()) __VERIFIER_assert(inv1(x2, n2));
    else __VERIFIER_assert(inv2(y2, n2));
    assume(0);
  }

  sassert(y2 == n2);
}
