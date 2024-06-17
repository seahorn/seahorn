//; RUN: %sea "%s" --own-sem 2>&1 | OutputCheck %s
// CHECK: ^unsat$
#include "seahorn/seahorn.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>

extern bool nd_bool(void);
extern char nd_char(void);
extern void pretendEscapeToMemory(char *);

int main() {
  char *p = (char *)malloc(sizeof(char));
  SEA_MKOWN(p);
  char c = nd_char();
  assume (c == 0);
  SEA_WRITE_CACHE(p, c);
  *p = c;
  char *b;
  SEA_BORROW(b, p);
  if (nd_bool()) {
    c = nd_char();
    assume(c > 1);
    SEA_WRITE_CACHE(b, c);
    *b = c;
    pretendEscapeToMemory(b);
  }
  SEA_DIE(b);
  char r;
  SEA_READ_CACHE(r, p);
  sassert(r == 0 || r > 1);
  SEA_DIE(p);
  return 0;
}
