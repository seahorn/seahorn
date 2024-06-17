//; RUN: %sea "%s" "-g" --own-sem 2>&1 | OutputCheck %s
// CHECK: ^unsat$
#include "seahorn/seahorn.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>

extern char nd_char();

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
  h0->valid = false;
  SEA_WRITE_CACHE(h0, false);
  // No need to set fatptr_slot1
  // A correct non deterministic value is read from slot1
  // SEA_SET_FATPTR_SLOT1(h0, h00, 0xA);
  bool *h0b0_valid;
  SEA_BORROW_OFFSET(h0b0_valid, h0, offsetof(Handle, valid));

  // write to cache and mem
  SEA_WRITE_CACHE(h0b0_valid, true);
  *h0b0_valid = true;
  SEA_DIE(h0b0_valid);
  bool valToAssert;
  char *r = (char *)h0;
  SEA_READ_CACHE(valToAssert, r);
  sassert(valToAssert == true);

  Handle *h1b;
  // Two level borrow
  SEA_BORROW(h1b, h0);
  bool *h1b_valid, *h2b_valid;
  SEA_BORROW_OFFSET(h1b_valid, h1b, offsetof(Handle, valid));
  // When writing to memory, also write to cache.
  SEA_WRITE_CACHE(h1b_valid, false);
  *h1b_valid = false;
  SEA_DIE(h1b_valid);
  SEA_DIE(h1b);
  // It is valid to read from cache instead of memory
  // since h11u is unique;
  bool v;
  char *hr = (char *)h0;
  SEA_READ_CACHE(v, hr);
  sassert(v == false);

  return 0;
}
