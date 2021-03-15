// RUN: %sea smt %s --step=small -o %t.smt2
// RUN: %z3 %t.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
// CHECK: ^sat$

#include "seahorn/seahorn.h"

extern int nd1();
extern int nd2();
extern int nd3();
extern int nd4();

// Loop invariant.
extern bool infer(int x, int n);
bool PARTIAL_FN inv(int x, int n) { return infer(x, n); }

// Test.
int main(void) {
  // See 03_loop.unsat.c.
  //
  // The inductive invariant is now restricted to x and n. It is impossible to
  // say that x == y. Therefore, there is no solution that satisfies the
  // property. Hence, the problem is SAT.

  int x1 = 0;
  int y1 = 0;
  int n1 = nd1();
  assume(n1 > 0);

  __VERIFIER_assert(inv(x1, n1));

  int x2 = nd2();
  int y2 = nd3();
  int n2 = nd4();
  assume(inv(x2, n2));
  if (x2 < n2) {
    x2 += 1; y2 += 1;
    __VERIFIER_assert(inv(x2, n2));
    assume(0);
  }

  sassert(y2 == n2);
}
