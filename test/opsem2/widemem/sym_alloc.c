//; RUN: %sea "%s" --horn-bv2-extra-widemem --horn-opsem-max-symb-alloc=0 2>&1 | OutputCheck %s
//; RUN: %sea "%s" --horn-bv2-widemem --horn-opsem-max-symb-alloc=0 2>&1 | OutputCheck %s
// CHECK: ^sat$

/**
 * This test should normally be unsat except that we don't give any symbolic memory (--horn-opsem-max-symb-alloc=0) so
 * seahorn nondeterministically chooses two fresh pointers.
 *
 * This test SHOULD NOT crash.
 */

#include <seahorn/seahorn.h>
#include <stdlib.h>

extern uint8_t nd_char();
extern bool nd_bool();

int main() {
  size_t szBytes1 = nd_char();
  size_t szBytes2 = nd_char();

  assume(szBytes1 < 100);
  assume(szBytes1 < 100);
  uint32_t *p = malloc(szBytes1 * sizeof(uint8_t));
  uint32_t *q = malloc(szBytes2 * sizeof(uint8_t));
  *p = 1;
  *q = 2;
  int diff = p - q;
  sassert(diff < -4 || diff > 4);
  sassert(*p != *q);
}


