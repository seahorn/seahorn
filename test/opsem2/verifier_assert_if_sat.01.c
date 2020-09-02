//; RUN: %sea "%s" 2>&1 | OutputCheck %s
// CHECK: ^Error: assertion failed
// CHECK: ^sat$

#include "seahorn/seahorn.h"

extern int nd_int(void);

int main(int argc, char **argv) {
  int a = nd_int();
  int b = nd_int();
  __VERIFIER_assume(a == 5);
  __VERIFIER_assume(b == 10);
  __VERIFIER_assert_if(a == 5, b != 10);
  sassert(!(a == 5 && b == 10));
  return 0;
}
