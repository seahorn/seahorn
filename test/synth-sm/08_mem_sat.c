// RUN: %sea smt %s --step=small -o %t.smt2
// RUN: %z3 %t.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
// CHECK: ^sat$

#include "seahorn/seahorn.h"

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
  // See 08_mem_unsat.c.
  //
  // Property: If a reactive system implements body, then it is always the case
  //           that v[i] <= sum.
  //
  // This property does not hold. As PCMC is sound, a compositional invariant
  // does not exist. Therefore, the program is SAT.

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
    sassert(v == sum);

    // END_TX[
    __VERIFIER_assert(inv(owner, sum, i, v));
    __VERIFIER_assert(inv(owner, sum, j, v_j));
    // ]END
  }
}
