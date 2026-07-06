// RUN: %sea --assert-on-backedge --horn-unify-assumes=true --horn-vcgen-only-dataflow=true --horn-bmc-coi=true --horn-gsa "%s" 2>&1 | filecheck %s
// CHECK-NOT: {{^Error: vacuity failed}}
// CHECK: {{^Error: assertion failed}}
// CHECK: {{^unsat$}}

#include "seahorn/seahorn.h"

extern int nd_int(void);

int main(int argc, char **argv) {
  int c = nd_int();
  int limit = nd_int();
  __VERIFIER_assume(c == 2);
  __VERIFIER_assume(limit == 20);
  while (c < limit) {
    c *= 2;
  }
  if (c > limit) sassert(c >= 20);
  return 0;
}
