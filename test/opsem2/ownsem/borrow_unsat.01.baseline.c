//; RUN: %sea "%s" --own-sem 2>&1 | OutputCheck %s
// CHECK: ^unsat$
#include "seahorn/seahorn.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>

extern char nd_char();
extern void pretendEscapeToMemory(char *);

typedef struct handle_t {
  unsigned val;
  bool valid;
} Handle;

int main() {
  sea_tracking_on();

  Handle *h0 = (Handle *)malloc(sizeof(Handle));
  h0->val = 0;
  h0->valid = false;

  SEA_MKOWN(h0);

  SEA_WRITE_CACHE(h0, false);

  bool *h0b0_valid;
  SEA_BORROW_OFFSET(h0b0_valid, h0, offsetof(Handle, valid));

  pretendEscapeToMemory((char *)h0b0_valid);

  // write to cache and mem
  *h0b0_valid = true;

  SEA_WRITE_CACHE(h0b0_valid, true);
  SEA_DIE(h0b0_valid);
  bool valToAssert;
  SEA_READ_CACHE(valToAssert, (char *)h0);
  // NOTE: Comment out one of the aaserts
  // to see coi in action.
  // In case we are asserting on cached
  // value only, there should be fewer
  // memory accesses.
  sassert(valToAssert == true);
  sassert(h0->valid);
  return 0;
}
