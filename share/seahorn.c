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

int32_t get_value_i32(int ctr_arg, int32_t *g_arr, int g_arr_sz) {
  static int ctr = 0;
  assert (ctr == ctr_arg);
  assert (ctr < g_arr_sz);
  return g_arr[ctr++];
}
