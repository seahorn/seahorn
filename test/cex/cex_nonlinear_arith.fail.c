// RUN: %sea exe-cex -O0 --verify "%s" 2>&1 | OutputCheck %s
// CHECK: ^__VERIFIER_error was not executed$

/* 
   Example where SeaHorn's back-end solver produces an spurious cex
   which is not valid at the bit-level. The reason is that the solver
   does not reason about non-linear multiplication.
*/

#include "seahorn/seahorn.h"

extern int nd_int(void);

int main(int argc, char**argv) {
  int x = nd_int();
  __VERIFIER_assume (x >= 2);
  __VERIFIER_assume (x <= 100);  
  int y = x * x;
  if (y == x) {
    __VERIFIER_error();
  }
  return 0;
}
