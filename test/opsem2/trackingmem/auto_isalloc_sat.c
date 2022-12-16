//; RUN: %fpfsea "%s" --horn-bv2-extra-widemem --horn-bv2-tracking-mem --add-isalloc-check 2>&1 | OutputCheck %s
// CHECK: ^sat$

#include "seahorn/seahorn.h"
#include <stdlib.h>

extern void sea_reset_modified(char *);
extern bool sea_is_alloc(char *);
extern void sea_tracking_on();
extern void sea_tracking_off();
extern void sea_free(char *);
extern int nd_int();
int main() {
  sea_tracking_on();
  int *a = malloc(1024);
  sea_free((char *)a);
  *a = nd_int();
  return 0;
}
