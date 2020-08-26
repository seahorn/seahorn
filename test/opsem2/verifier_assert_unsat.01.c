// RUN: %sea --horn-unify-assumes=true --horn-vcgen-only-dataflow=true --horn-bmc-coi=true "%s" 2>&1 | OutputCheck %s
// CHECK: ^Error: Antecedent is unsat
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

extern int nd_int(void);

int main(int argc, char **argv) {
  int a = nd_int();
  __VERIFIER_assume(a < 10);
  if (a > 0) {
    __VERIFIER_assume(a == 100);
    __VERIFIER_assert(a == 100);
    sassert(a == 100);
  }
  return 0;
}
