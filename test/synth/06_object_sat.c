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
extern int nd7();
extern int nd8();
extern int nd9();

// Object invariant.
extern bool infer(int count, int max);
bool PARTIAL_FN inv(int count, int max) { return infer(count, max); }

// Object methods.
void incr(int *count, int *max) {
  if (*count < *max) ++(*count);
}

void decr(int *count, int *max) {
  if (*count > 0) --(*count);
}

void set(int *count, int *max, int nMax) {
  assume(nMax > 0);
  *count = 0;
  *max = nMax;
}

int check(int *count, int *max) {
  return (*count >= *max);
}

// Test.
int main(void) {
  // See 05_object_unsat.c.
  //
  // The specification is now count < max, which is not true of the program.
  // Hence, the program is SAT.

  // constructor => inv
  int count1 = 0;
  int max1 = nd1();
  assume(max1 > 0);
  __VERIFIER_assert(inv(count1, max1));

  // inv && op => inv'
  int count2 = nd2();
  int max2 = nd3();
  assume(inv(count2, max2));
  if (nd4()) incr(&count2, &max2);
  else if (nd5()) decr(&count2, &max2);
  else if (nd6()) set(&count2, &max2, nd7());
  else check(&count2, &max2);
  __VERIFIER_assert(inv(count2, max2));

  // inv => safe
  int count3 = nd8();
  int max3 = nd9();
  assume(inv(count3, max3));
  sassert(count3 < max3);
}
