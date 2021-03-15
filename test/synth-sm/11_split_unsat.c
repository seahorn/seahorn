// RUN: %sea smt %s --step=small -o %t.smt2
// RUN: %z3 %t.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

extern int nd1();
extern int nd2();
extern int nd3();
extern int nd4();
extern int nd5();

// Compositional invariant.
extern bool infer(int sum, int v);
bool PARTIAL_FN inv1(int sum, int v) {
  if (v == 0) return 1;
  return infer(sum, v);
}
bool PARTIAL_FN inv2(int sum, int v) {
  if (v == 0) return 1;
  return infer(sum, v);
}

// Test.
int main(void) {
  // see 07_mem_unsat.c.

  int owner = nd1();
  int sum = 0;

  while (1) {
    int i = nd2();

    // START_TX[
    int j = nd3();
    int v = nd4();
    int v_j = nd5();
    assume(i != j);
    if (i == owner) assume(inv1(sum, v));
    else assume(inv2(sum, v));
    if (j == owner) assume(inv1(sum, v_j));
    else assume(inv2(sum, v_j));
    // ]END

    if (i != owner) {
      v += 1;
      sum += 1;
    }
    sassert(v <= sum);

    // END_TX[
    if (i == owner) __VERIFIER_assert(inv1(sum, v));
    else __VERIFIER_assert(inv2(sum, v));
    if (j == owner) __VERIFIER_assert(inv1(sum, v_j));
    else __VERIFIER_assert(inv2(sum, v_j));
    // ]END
  }
}
