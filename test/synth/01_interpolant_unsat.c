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
  // p1 := (w != 0)
  // p2 := (y = 2 * z + 6)
  // p3 := (x < 7)
  // p4 := (y == -4 * z)
  // p5 := (y != 4)
  //
  // A(w, y, z) := p1 && p2
  // B(x, y, z) := p3 && p4 && p5 
  //
  // A is SAT with solution { w := 1, y := 0, z := -3 }. B is also SAT, with
  // solution { x := 0, y := 0, z := 0 }. However, A && B is UNSAT. First,
  // resolve p2 with p4 to obtain p6 := z = -1. Next, resolve p6 with p4 to
  // obtain p7 := y = -4. Finally, p7 conflicts with p5.
  //
  // Therefore, there exists an interpolant, ITP(y, z), such that A(w, y, z)
  // implies ITP(y, z) and ITP(y, z) implies the negation of B(w, y, z).
  //
  // Therefore, any solution for itp entails the safety of the program.
  //
  // Note: z3's certificate is `true` because a single substitution of `itp` is
  //       sufficient to prove: `!((x2 < 7) && (y2 == -4 * z2) && (y2 != 4))`.

  int w1 = nd1();
  int y1 = nd2();
  int z1 = nd3();
  assume((w1 != 0) && (y1 == 2 * z1 + 6));
  __VERIFIER_assert(itp(y1, z1));

  int x2 = nd4();
  int y2 = nd5();
  int z2 = nd6();
  assume(itp(y2, z2));
  sassert(!((x2 < 7) && (y2 == -4 * z2) && (y2 != 4)));
}
