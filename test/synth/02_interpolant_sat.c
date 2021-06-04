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

// Interpolant.
extern bool infer(int y, int z);
bool PARTIAL_FN itp(int y, int z) { return infer(y, z); }

// Test.
int main(void) {
  // See 01_interpolant_unsat.c.
  // 
  // Recall that the original program was safe because (1) A && B entailed
  // y = 4 and (2) B entails y != 4. In this program, B no longer entails
  // y != 4. As a result, A && B are SAT, and an interpolant no longer exists.
  // The program is unsafe.

  int w1 = nd1();
  int y1 = nd2();
  int z1 = nd3();
  assume((w1 != 0) && (y1 = 2 * z1 + 6));
  __VERIFIER_assert(itp(y1, z1));

  int x2 = nd4();
  int y2 = nd5();
  int z2 = nd6();
  assume(itp(y2, z2));
  sassert(!((x2 < 7) && (y2 == -4 * z2)));
}
