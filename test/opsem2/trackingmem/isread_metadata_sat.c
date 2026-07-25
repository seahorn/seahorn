//; RUN: %sea "%s" --horn-bv2-extra-widemem --horn-bv2-tracking-mem 2>&1 | filecheck %s
// CHECK: {{^sat$}}

// Read metadata is set, so sea_is_read() must observe it and the assertion
// must fail. Guards the visitIsRead implementation in BvOpSem2 and the
// "sea.is_read" entry in DfCoiAnalysis: without the latter the preceding
// shadow.mem.load is pruned under COI, sea_is_read yields no register, and
// the result is a vacuous sat rather than this one.

#include "seahorn/seahorn.h"
#include <stdbool.h>
#include <stdlib.h>

extern bool sea_is_read(char *);
extern void sea_set_shadowmem(char, char *, size_t);
extern void sea_tracking_on();
extern void sea_tracking_off();
extern void memhavoc(void *, size_t);

int main(int argc, char **argv) {
  sea_tracking_on();
  char *buf = (char *)malloc(8);
  memhavoc(buf, 8);
  sea_set_shadowmem(TRACK_READ_MEM, buf, 1);
  // this assert will fail
  sassert(!sea_is_read(buf));
  sea_tracking_off();
  return 0;
}
