// RUN: %sea --horn-unify-assumes=true --horn-vcgen-only-dataflow=true --horn-bmc-coi=true "%s" 2>&1 | OutputCheck %s
// CHECK: ^Error: Consequent is sat
// CHECK: ^sat$

#include "seahorn/seahorn.h"

extern int nd_int(void);

int main(int argc, char **argv) {
  int a = nd_int();
  __VERIFIER_assume(a == 10);
  if (a > 0) {
    __VERIFIER_assert(a == 99);
    sassert(a == 99);
  }
  return 0;
}
