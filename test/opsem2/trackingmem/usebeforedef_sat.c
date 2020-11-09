//; RUN: %sea "%s" --horn-bv2-extra-widemem --horn-bv2-tracking-mem 2>&1 | OutputCheck %s
// CHECK: ^sat$

#include "seahorn/seahorn.h"

extern bool sea_is_modified(char *);

int main(int argc, char **argv) {
  int a;
  sassert(sea_is_modified((char *)&a));
  return 0;
}
