//; RUN: %sea "%s" --horn-bv2-extra-widemem --horn-bv2-tracking-mem 2>&1 | filecheck %s
// CHECK: {{^unsat$}}

// Same program as load_is_def_sat.c but WITHOUT
// --horn-shadow-mem-load-is-def. Loads stay MemUses, no read metadata is
// stamped, sea_is_read(buf) is false and the assertion holds. This pins the
// default: making every load a MemDef adds a memory version per load and
// grows the VC, so it must stay opt-in.

#include "seahorn/seahorn.h"
#include <stdbool.h>
#include <stdlib.h>

extern bool sea_is_read(char *);
extern void sea_reset_read(char *);
extern void sea_tracking_on();
extern void sea_tracking_off();
extern void memhavoc(void *, size_t);

int main(int argc, char **argv) {
  sea_tracking_on();
  char *buf = (char *)malloc(8);
  memhavoc(buf, 8);
  sea_reset_read(buf);
  char v = buf[0];
  sassert(v == 0 || !sea_is_read(buf));
  sea_tracking_off();
  return 0;
}
