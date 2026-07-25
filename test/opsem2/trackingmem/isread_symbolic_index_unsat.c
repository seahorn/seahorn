//; RUN: %sea "%s" --horn-bv2-extra-widemem --horn-bv2-tracking-mem --horn-shadow-mem-load-is-def 2>&1 | filecheck %s
// CHECK: {{^unsat$}}

// Read metadata must be keyed per ADDRESS, not per allocation: a load at a
// symbolic index must mark only the element it actually touched.
//
// The other tests here index with constants, which are folded so each element
// presents a distinct pointer base -- they pass even when metadata is keyed by
// the allocation base, and so cannot observe this class of defect. A symbolic
// index keeps the displacement in the pointer's offset field, which is exactly
// where the information used to be dropped, collapsing every element of the
// object onto one metadata slot.
//
// Here t[i] is loaded with i pinned to 2, so t[0] must remain unread. If
// metadata degrades to allocation granularity this assertion fails and the
// test reports sat.

#include "seahorn/seahorn.h"
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

extern bool sea_is_read(char *);
extern void sea_reset_read(char *);
extern void sea_tracking_on();
extern void sea_tracking_off();
extern void memhavoc(void *, size_t);
extern uint32_t nd_u32();

// keeps the load live; a load outside the assertion's cone of influence is
// optimized away before it can stamp anything
volatile uint32_t g_sink;

int main(int argc, char **argv) {
  uint32_t t[8];
  sea_tracking_on();
  memhavoc(t, sizeof(t));

  uint32_t i = nd_u32();
  assume(i < 8);
  assume(i == 2);

  for (unsigned k = 0; k < 8; ++k)
    sea_reset_read((char *)&t[k]);

  g_sink = t[i];

  sassert(!sea_is_read((char *)&t[0]));
  sea_tracking_off();
  return 0;
}
