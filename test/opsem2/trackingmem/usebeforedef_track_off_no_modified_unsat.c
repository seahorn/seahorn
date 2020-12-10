//; RUN: %sea "%s" --horn-bv2-extra-widemem --horn-bv2-tracking-mem 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

extern bool sea_is_modified(char *);
extern void sea_tracking_on();
extern void sea_tracking_off();

int main(int argc, char **argv) {
  int a;
  // turn tracking on but it will not affect preceding statements.
  sea_tracking_on();
  sassert(!sea_is_modified((char *)&a));
  return 0;
}
