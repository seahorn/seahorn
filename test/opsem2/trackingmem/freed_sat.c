//; RUN: %sea "%s" --horn-bv2-extra-widemem --horn-bv2-tracking-mem 2>&1 | OutputCheck %s
// CHECK: ^sat$

#include "seahorn/seahorn.h"
#include <stdlib.h>

extern void sea_reset_modified(char *);
extern bool sea_is_alloc(char *);
extern void sea_tracking_on();
extern void sea_tracking_off();

extern int nd_int();
int main() {
  sea_tracking_on();
  int *a = malloc(1024);
  *a = nd_int();
  sassert(!sea_is_alloc((char *) a));
  return 0;
}
