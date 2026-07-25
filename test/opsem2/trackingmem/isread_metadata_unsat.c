//; RUN: %sea "%s" --horn-bv2-extra-widemem --horn-bv2-tracking-mem 2>&1 | filecheck %s
// CHECK: {{^unsat$}}

// Negative control for isread_metadata_sat.c: read metadata is cleared, so
// sea_is_read() must report false and the assertion must hold. Together the
// pair shows sea_is_read tracks the metadata rather than returning a constant
// or an unconstrained value.

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
  sea_set_shadowmem(TRACK_READ_MEM, buf, 0);
  sassert(!sea_is_read(buf));
  sea_tracking_off();
  return 0;
}
