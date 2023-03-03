//; RUN: %sea "%s" --ignore-def-verifier-fn=false 2>&1 | OutputCheck %s
// CHECK: ^unsat$

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
  sassert(a == 5 && b == 10);
  return 0;
}
