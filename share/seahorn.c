#include <stdint.h>
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>

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

void* __seahorn_get_value_ptr (int ctx, void* *g_arr, int g_arr_sz)
{
  printf ("WARNING: pointers not supported. Returning NULL\n");
  return NULL;
}
