// RUN: %sea --horn-unify-assumes=true --horn-vcgen-only-dataflow=true --horn-bmc-coi=true "%s" 2>&1 | OutputCheck %s
// CHECK: ^Error: vacuity failed
// CHECK-NOT: ^Error: assertion failed
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

extern int nd_int(void);

int main(int argc, char **argv) {
  int a = nd_int();
  __VERIFIER_assume(a < 10);
  if (a > 0) {
    __VERIFIER_assume(a == 100);
    __VERIFIER_assert_not(a == 100);
    sassert(a != 100);
  }
  return 0;
}
