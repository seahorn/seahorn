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
// CHECK: ^unsat$

#include "seahorn/seasynth.h"

extern int nd1();
extern int nd2();
extern int nd3();
extern int nd4();

// Loop invariant.
extern bool infer(int x, int y, int n);
bool PARTIAL_FN inv(int x, int y, int n) { return infer(x, y, n); }

// Test.
int main(void) {
  // Problem:
  //   int x = 0;
  //   int y = 0;
  //   int n = *;
  //   assume(n > 0);
  //
  //   while (x < n) {
  //     x += 1; y += 1;
  //   }
  //
  //   sassert(y == n);
  // The program is safe because (x <= n && x == y) is an invariant of the loop.
  // The loop invariant is over all of (x, y, n), so a solution exists.

  int x1 = 0;
  int y1 = 0;
  int n1 = nd1();
  assume(n1 > 0);

  // Pre => Inv
  sassert(inv(x1, y1, n1));

  // Inv && cond && Tr => Inv'
  int x2 = nd2();
  int y2 = nd3();
  int n2 = nd4();
  assume(inv(x2, y2, n2));
  if (x2 < n2) {
    x2 += 1; y2 += 1;
    sassert(inv(x2, y2, n2));
    assume(0);
  }

  // Inv && !cond => Post
  sassert(y2 == n2);
}
