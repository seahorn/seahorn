//; RUN: %sea "%s" --horn-bv2-extra-widemem --horn-bv2-tracking-mem --horn-shadow-mem-load-is-def 2>&1 | filecheck %s
// CHECK: {{^unsat$}}

// Ordinary memory semantics must survive --horn-shadow-mem-load-is-def: a value
// stored is the value loaded back, on a buffer whose read metadata is observed
// and on one that is not.
//
// Regression test for a real defect. The first implementation made EVERY load a
// MemDef, including loads on DSA nodes that the interprocedural mod/ref summary
// classified read-only. Their call sites still passed the node as
// shadow.mem.arg.ref (in-only) while the callee now produced a new memory
// version, leaving shadow SSA inconsistent across the boundary. Two
// already-verified verify-c-common jobs (hash_table_create, hash_table_put)
// silently flipped unsat -> sat: spurious counterexamples on correct code, with
// no diagnostic. Loads are now emitted as MemDefs only for nodes whose read
// metadata is actually observed, and such nodes are additionally marked
// modified so the summary matches the defs emitted.
//
// `plain` exercises the untracked path (no MemDefs) and `tracked` the gated one
// (MemDefs), in one program so the two cannot drift apart.
//
// Indices are symbolic and only assumed equal, so the store/load pair cannot be
// discharged by store-to-load forwarding in the front end -- with constant
// indices the assertions fold away and seahorn reports "no assertion was found"
// rather than unsat.

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

int main(int argc, char **argv) {
  uint32_t *tracked = (uint32_t *)malloc(4 * sizeof(uint32_t));
  uint32_t *plain = (uint32_t *)malloc(4 * sizeof(uint32_t));
  memhavoc(tracked, 4 * sizeof(uint32_t));
  memhavoc(plain, 4 * sizeof(uint32_t));

  sea_tracking_on();
  // observing this buffer is what makes its node read-tracked, so only its
  // loads become MemDefs
  sea_reset_read((char *)tracked);

  uint32_t v = nd_u32();
  uint32_t i = nd_u32();
  uint32_t j = nd_u32();
  assume(i < 4);
  assume(j < 4);
  assume(i == j);

  plain[i] = v;
  sassert(plain[j] == v);

  tracked[i] = v;
  sassert(tracked[j] == v);

  sea_tracking_off();
  return 0;
}
