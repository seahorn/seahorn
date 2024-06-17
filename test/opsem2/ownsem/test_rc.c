//; RUN: %sea "%s" --own-sem 2>&1 | OutputCheck %s
// CHECK: ^unsat$
#include "seahorn/seahorn.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>

extern bool nd_bool(void);
extern char nd_char(void);
extern unsigned nd_unsigned(void);


int main() {
  unsigned x = nd_unsigned();
  unsigned y = nd_unsigned();
  unsigned rc = nd_unsigned();
  assume (rc == 1 + x - y);
  // sassert(rc == 1);
  assume(y == x);
  sassert(rc == 1);
  return 0;
}
