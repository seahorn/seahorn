//; RUN: %sea "%s" --own-sem --horn-vcgen-use-ite --horn-vcgen-only-dataflow
//--horn-bmc-coi 2>&1 | OutputCheck %s
// CHECK: ^unsat$
#include "seahorn/seahorn.h"
#include <stdbool.h>
#include <stdlib.h>

extern char nd_char();

typedef struct handle_t {
  unsigned val;
  bool valid;
} Handle;

int main() {
  sea_tracking_on();
  Handle *h1 = (Handle *)malloc(sizeof(Handle));
  Handle *h2 = (Handle *)malloc(sizeof(Handle));
  h1->val = 0;
  h1->valid = true;
  h2->val = 1;
  h2->valid = false;
  SEA_BEGIN_UNIQUE_AND_LOAD_CACHE(h1, h1->valid);

  // When writing to memory, also write to cache.
  SEA_WRITE_CACHE(h1, false);
  h1->valid = false;
  // It is valid to read from cache instead of memory
  // since h1 is unique;
  bool v;
  char *r = (char *)h1;
  SEA_READ_CACHE(v, r);
  sassert(v == false);
  r = (char *)h1;
  SEA_UNLOAD_CACHE_AND_END_UNIQUE(r, &h1->valid, 1);
  return 0;
}
