//; RUN: %sea "%s" --horn-bv2-extra-widemem --horn-bv2-tracking-mem 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

extern void sea_reset_modified(char *);
extern bool sea_is_modified(char *);
extern void sea_tracking_on();
extern void sea_tracking_off();

int main(int argc, char **argv) {
  sea_tracking_on();
  int a = 5;
  sea_reset_modified((char *)&a);
  int b = a + 1;
  sassert(!sea_is_modified((char *)&a));
  sea_tracking_off();
  return 0;
}
