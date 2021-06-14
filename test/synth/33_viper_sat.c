// RUN: %sea smt %s --step=small --inline -o %t.sm.inline.smt2
// RUN: %z3 %t.sm.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=large --inline -o %t.lg.inline.smt2
// RUN: %z3 %t.lg.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// CHECK: ^sat$

#include "seahorn/seasynth.h"

#include "viper_utils.inc"
#include "viper_copyAndInc.inc"

extern int nd1();
extern int nd2();
extern int nd3();
extern int nd4();
extern int nd5();
extern int nd6();
extern int nd7();
extern int nd8();
extern int nd9();
extern int nd10();
extern int nd11();
extern int nd12();
extern int nd13();

int main(void) {
  // Problem: infer a feasible footprint for copyAndInc.
  int rule = nd1();
  if (rule == 0)
  {
    // Selects inputs non-deterministically.
    int xf_acc = nd2();
    int xf_val = nd3();
    int yf_acc = nd4();
    int yf_val = nd5();

    // Ensures that permissions are valid.
    assume(is_valid_perm(xf_acc));
    assume(is_valid_perm(yf_acc));

    // Calls method.
    copyAndInc_Permissions(xf_acc, xf_val, yf_acc, yf_val);
  }
  else if (rule == 1)
  {
    // Selects inputs non-deterministically.
    int xf_acc = nd6();
    int xf_val = nd7();
    int yf_acc = nd8();
    int yf_val = nd9();

    // Ensures that permissions are valid.
    assume(is_valid_perm(xf_acc));
    assume(is_valid_perm(yf_acc));

    // Calls method.
    copyAndInc_safety(xf_acc, xf_val, yf_acc, yf_val);
  }
  else
  {
    // If xf_acc and yf_acc do not exceed ACC_FULL, unsafe aliasing will occur.
    int xf_acc = nd10();
    int yf_acc = nd11();
    int xf_acc_n = nd12();
    int yf_acc_n = nd13();
    assume(CalleePermissions(xf_acc, yf_acc, xf_acc_n, yf_acc_n));
    sassert(xf_acc + yf_acc <= ACC_FULL);
  }
  return 0;
}
