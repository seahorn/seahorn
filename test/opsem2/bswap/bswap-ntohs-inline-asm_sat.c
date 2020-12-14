//; RUN: %sea "%s" 2>&1 | OutputCheck %s
// CHECK: ^Error: assertion failed
// CHECK: ^sat$

#include "seahorn/seahorn.h"
#include <arpa/inet.h>
#include <stdio.h>

extern uint16_t nd_uint16_t(void);

int main(int argc, char **argv) {
  uint16_t a = nd_uint16_t();
  uint16_t b = nd_uint16_t();
  __VERIFIER_assume(a == b);
  uint16_t res_a = ntohs(a);
  uint16_t res_b = ntohs(b);
  __VERIFIER_assert(res_a != res_b);
  sassert(res_a != res_b);
  return 0;
}
