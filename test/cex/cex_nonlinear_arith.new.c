// RUN: %solve --horn-bmc-engine=mono --horn-bv2-lambdas=false --horn-bmc --horn-bv2=true --cex=/tmp/test_cex_nonlinear_arith.ll %s > /dev/null 2>&1
// RUN: %cex --run -g %s /tmp/test_cex_nonlinear_arith.ll 2>&1 | OutputCheck %s

// CHECK: ^__VERIFIER_error was executed$

/* 
   XXX: how to reproduce spurious cex?
   Example where SeaHorn's back-end solver produces an spurious cex
   which is not valid at the bit-level. The reason is that the solver
   does not reason about non-linear multiplication.
*/

#include "seahorn/seahorn.h"

extern int nd_int(void);

int main(int argc, char**argv) {
  int x = nd_int();
  assume (x >= 1);
  assume (x <= 100);
  int y = x * x;
  if (y > x) {
    __VERIFIER_error();
  }
  return 0;
}
