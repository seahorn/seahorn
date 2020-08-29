// RUN: %sea --assert-on-backedge --horn-unify-assumes=true --horn-vcgen-only-dataflow=true --horn-bmc-coi=true "%s" 2>&1 | OutputCheck %s
// CHECK-NOT: ^Error: Antecedent is unsat
// CHECK: ^Error: Consequent is sat
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

extern int nd_int(void);

int main(int argc, char **argv) {
  int c = nd_int();
  int limit = nd_int();
  __VERIFIER_assume(c == 2);
  __VERIFIER_assume(limit == 10);
  while (c < limit) {
    c++;
  }
  sassert(c == 9);
  return 0;
}
