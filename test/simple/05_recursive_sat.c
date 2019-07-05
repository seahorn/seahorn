// RUN: %sea pf "%s" --step=small --inline 2>&1 | OutputCheck %s
// CHECK: ^sat$

#include "seahorn/seahorn.h"

int id(int x);
int id2(int x);

int id(int x) {
  if (x == 0)
    return 0;
  int ret = id2(x - 1) + 1;
  if (ret > 2)
    return 2;
  return ret;
}

int id2(int x) {
  if (x == 0)
    return 0;
  int ret = id(x - 1) + 1;
  if (ret > 2)
    return 2;
  return ret;
}

int main(void) {
  int input = __VERIFIER_nondet_int();
  int result = id(input);
  sassert(result == 3);
}
