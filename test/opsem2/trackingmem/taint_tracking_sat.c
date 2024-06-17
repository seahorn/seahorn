//; RUN: %sea "%s" --horn-bv2-extra-widemem --horn-bv2-tracking-mem 2>&1 | OutputCheck %s
// CHECK: ^sat$

#include "seahorn/seahorn.h"
#include <stdbool.h>
extern void sea_set_shadowmem(char, char*, size_t);
extern size_t sea_get_shadowmem(char, char*);
extern void sea_tracking_on();
extern void sea_tracking_off();
extern bool nd_bool();

int main(int argc, char **argv) {
  sea_tracking_on();
  int a = 5;
  bool c = nd_bool();
  size_t m = 0;
  if (c) {
    m = 10;
  } else {
    m = 20;
  }
  sea_set_shadowmem(3, (char *)&a, m);
  size_t r = sea_get_shadowmem(3, (char *)&a);
  if (c) {
    sassert(r == 10);
  } else {
    // this assert will fail
    sassert(r == 21);
  }
  sea_tracking_off();
  return 0;
}
