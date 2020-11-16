//; RUN: %sea "%s" --horn-bv2-extra-widemem --horn-bv2-tracking-mem 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

extern void sea_reset_modified(char *);
extern bool sea_is_modified(char *);

int main(int argc, char **argv) {
  int a = 5;
  sea_reset_modified((char *)&a);
  int b = a + 1;
  sassert(!sea_is_modified((char *)&a));
  return 0;
}
