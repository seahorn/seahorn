//; RUN: %sea "%s" -g -S --own-sem 2>&1 | OutputCheck %s
// CHECK: ^sat$
#include "seahorn/seahorn.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
extern char nd_char();
extern void pretendEscapeToMemory(char *);
extern __declspec(noalias) void sea_printf(const char *format, ...);

static unsigned CLEAN = 0;
static unsigned TAINT = 1;

typedef struct handle_t {
  uint32_t *own_uint32ptr;
  bool valid;
} Handle;

int main() {
  sea_tracking_on();
  Handle *h0 = (Handle *)malloc(sizeof(Handle));

  uint32_t *stuff = (uint32_t *)malloc(sizeof(uint32_t));
  SEA_MKOWN(stuff);
  *stuff = CLEAN;
  h0->own_uint32ptr = stuff;
  h0->valid = false;
  pretendEscapeToMemory((char *)h0);
  uint32_t *bor_ptr;

  SEA_BORROW_LOAD(bor_ptr, &h0->own_uint32ptr);
  uint32_t r;
  SEA_READ_CACHE(r, (char *)bor_ptr);
  sea_printf("Cache val after first load:%d\n", r);
  SEA_WRITE_CACHE(bor_ptr, 1);
  SEA_READ_CACHE(r, (char *)bor_ptr);
  sea_printf("Cache val after first write:%d\n", r);
  *bor_ptr = TAINT;

  // NOTE: The following DIE is missing and hence the next BORROW_LOAD fails.
  // SEA_DIE(bor_ptr);

  uint32_t *bor_ptr2;
  SEA_BORROW_LOAD(bor_ptr2, &h0->own_uint32ptr);
  uint32_t bor_val;
  SEA_READ_CACHE(bor_val, (char *)bor_ptr2);
  sea_printf("Cache val after second load:%d\n", bor_val); 
  sassert(bor_val == TAINT);
  return 0;
}
