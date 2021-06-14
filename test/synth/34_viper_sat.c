// RUN: %sea smt %s --step=small --inline -o %t.sm.inline.smt2
// RUN: %z3 %t.sm.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=large --inline -o %t.lg.inline.smt2
// RUN: %z3 %t.lg.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// CHECK: ^sat$

#include "seahorn/seasynth.h"

#include "viper_utils.inc"

// Non-determinism.
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

// Assumes that the body of copyAndInc is unknown.
bool CalleePermissions(int xf_acc_0, int yf_acc_0, int xf_acc_n, int yf_acc_n)
{
  (void) xf_acc_0;
  (void) yf_acc_0;
  (void) xf_acc_n;
  (void) yf_acc_n;
  return true;
}

#include "viper_client.inc"

// Verification.
int main(void) {
  // Problem: infer a footprint for copyAndInc that satisfies client.
  int rule = nd1();
  if (rule == 0)
  {
    // Selects inputs non-deterministically.
    int af_acc = nd2();
    int af_val = nd3();
    int bf_acc = nd4();
    int bf_val = nd5();

    // Ensures that permissions are valid.
    assume(is_valid_perm(af_acc));
    assume(is_valid_perm(bf_acc));

    // Calls method.
    client_permissions(af_acc, af_val, bf_acc, bf_val);
  }
  else if (rule == 1)
  {
    // Selects inputs non-deterministically.
    int af_acc = nd6();
    int af_val = nd7();
    int bf_acc = nd8();
    int bf_val = nd9();

    // Ensures that permissions are valid.
    assume(is_valid_perm(af_acc));
    assume(is_valid_perm(bf_acc));

    // Calls method.
    client_safety(af_acc, af_val, bf_acc, bf_val);
  }
  else
  {
    // If `yf_acc == ACC_FULL`, then in client `y.f != 3` is feasible.
    int xf_acc = nd10();
    int yf_acc = nd11();
    int xf_acc_n = nd12();
    int yf_acc_n = nd13();
    assume(CallerPermissions(xf_acc, yf_acc, xf_acc_n, yf_acc_n));
    sassert(yf_acc == ACC_FULL);
  }
  return 0;
}
