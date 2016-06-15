#include <stdint.h>
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <string.h>

void __VERIFIER_error() {
  printf("__VERIFIER_error was executed\n");
  exit(1);
}

void __VERIFIER_assume(int x) {
  assert(x);
}

#define get_value_helper(ctype, llvmtype)              \
  ctype __seahorn_get_value_ ## llvmtype (int ctr, ctype *g_arr, int g_arr_sz) { \
    assert (ctr < g_arr_sz && "Unexpected index"); \
    return g_arr[ctr]; \
  }

#define get_value_int(bits) get_value_helper(int ## bits ## _t, i ## bits)

get_value_int(64)
get_value_int(32)
get_value_int(16)
get_value_int(8)

get_value_helper(intptr_t, ptr)

/** Dummy implementation of memory wrapping functions */

void __sea_mem_store (void *src, void *dst, size_t sz)
{
  /* if dst is a legal address */
  memcpy (dst, src, sz);
  /* else if dst is illegal, do nothing */
}

void __sea_mem_load (void *dst, void *src, size_t sz)
{
  /* if src is a legal address */
  memcpy (dst, src, sz);
  /* else, if src is illegal, return a dummy value */
}
