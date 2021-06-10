// RUN: %sea smt %s --step=small -o %t.sm.smt2
// RUN: %z3 %t.sm.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=small --inline --log=inline -o %t.sm.inline.smt2
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
extern int nd5();

// Compositional invariant.
extern bool infer(int owner, int sum, int i, int v);
bool PARTIAL_FN inv(int owner, int sum, int i, int v) {
  if (v == 0) return 1;
  return infer(owner, sum, i, v);
}

// Test.
int main(void) {
  // Assumption: init => forall i: m[i] = 0
  // Program:
  //   mapping(int => int) m;
  //   int owner;
  //   int sum = 0;
  //   
  //   void body(int i) {
  //     if (i == owner) {
  //       v += 1; sum += 1;
  //     }
  //   }
  // Property: If a reactive system implements body, then it is always the case
  //           that v[i] <= sum.
  //
  // A (sound but incomplete) solution to the above problem is to find a
  // compositional invariant Inv such that:
  // 1. Init => Inv
  // 2. Inv(i) && Tr(i) => Inv'(i)
  // 3. Inv(i) && i != j && Tr(i) && Inv(j) => Inv'(i)
  // In this case, such an invariant does exist and the program must be UNSAT.

  int owner = nd1();
  int sum = 0;

  while (1) {
    int i = nd2();

    // START_TX[
    int j = nd3();
    int v = nd4();
    int v_j = nd5();
    assume(i != j);
    assume(inv(owner, sum, i, v));
    assume(inv(owner, sum, j, v_j));
    // ]END

    if (i != owner) {
      v += 1;
      sum += 1;
    }
    sassert(v <= sum);

    // END_TX[
    sassert(inv(owner, sum, i, v));
    sassert(inv(owner, sum, j, v_j));
    // ]END
  }
}
