//; RUN: %sea "%s" 2>&1 | OutputCheck %s
// CHECK: ^sat$

#include "seahorn/seahorn.h"

#include "seahorn/seahorn.h"

// NOTE: these definition will be ignored by SEABMC
// However, they are added here as examples of verification
// in the presence of defined functions.
int sea_nd_int() { return 0; }
void __VERIFIER_assert(bool pred) {}
void __VERIFIER_error() {}
void __SEA_assume(bool pred) {}

int main(int argc, char **argv) {
  int a = sea_nd_int();
  int b = sea_nd_int();
  assume(a == 5);
  assume(b == 10);
  // a should be 5
  sassert(a == 6 && b == 10);
  return 0;
}
