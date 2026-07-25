//; RUN: %sea "%s" --horn-bv2-extra-widemem --horn-bv2-tracking-mem --horn-shadow-mem-load-is-def 2>&1 | filecheck %s
// CHECK: {{^sat$}}

// Under --horn-shadow-mem-load-is-def a load is emitted as a MemDef, so it
// has a write register and the opsem stamps read metadata at the loaded
// address. The load of buf[0] therefore makes sea_is_read(buf) true and the
// assertion fails.
//
// NOTE: the loaded value must appear INSIDE the assertion. If it does not,
// the load is not in the assertion's cone of influence and is optimized away
// before it can be observed, which yields unsat and looks exactly like the
// feature being absent.

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
  // this assert will fail: buf[0] was read, so the disjunct requires v == 0
  sassert(v == 0 || !sea_is_read(buf));
  sea_tracking_off();
  return 0;
}
