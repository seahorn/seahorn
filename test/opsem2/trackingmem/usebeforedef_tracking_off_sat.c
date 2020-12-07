//; RUN: %sea "%s" --horn-bv2-extra-widemem --horn-bv2-tracking-mem 2>&1 | OutputCheck %s
// CHECK: ^sat$

#include "seahorn/seahorn.h"

extern bool sea_is_modified(char *);
extern void sea_tracking_on();
extern void sea_tracking_off();

int main(int argc, char **argv) {
  sea_tracking_off();
  int a = 0;
  // setting track on after a store should have no effect on the store.
  sea_tracking_on();
  sassert(sea_is_modified((char *)&a));
  return 0;
}
