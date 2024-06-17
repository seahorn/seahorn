//; RUN: %sea "%s" -g -S --own-sem 2>&1 | OutputCheck %s
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

  SEA_WRITE_CACHE(h0, false);

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

  // Handle *h1s, *h1o1, *h1o;
  // Handle *h1b, *h1b1, *h1b2, *h1d;

  bool cacheVal;
  r = (char *)h0;
  SEA_READ_CACHE(cacheVal, r);
  h0->valid = cacheVal;
  SEA_MKSHR(h0);
  h0->val = 1;
  h0->valid = false;

  SEA_MKOWN(h0);
  SEA_WRITE_CACHE(h0, h0->valid);
  r = (char *)h0;
  SEA_READ_CACHE(valToAssert, r);
  sassert(valToAssert == false);
  Handle *h1b;
  SEA_BORROW(h1b, h0);
  SEA_DIE(h1b);
  bool *h1b_valid, *h2b_valid;
  SEA_BORROW_OFFSET(h1b_valid, h0, offsetof(Handle, valid));
  // When writing to memory, also write to cache.
  SEA_WRITE_CACHE(h1b_valid, false);
  *h1b_valid = false;

  SEA_DIE(h1b_valid);
  SEA_DIE(h1b);
  // It is valid to read from cache instead of memory
  // since h11u is unique;
  bool v;
  r = (char *)h0;
  SEA_READ_CACHE(v, r);
  sassert(v == false);
  return 0;
}
