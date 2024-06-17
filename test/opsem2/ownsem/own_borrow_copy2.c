//; RUN: %sea "%s" -g -S --horn-bmc-tactic=smtfd  --own-sem 2>&1 | OutputCheck %s
// CHECK: ^unsat$
#include "seahorn/seahorn.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>

extern bool nd_bool(void);
extern char nd_char(void);
extern void escapeToMemory(char *);

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
    char *cp1;
    SEA_BORROW(cp1, b);
    c = nd_char();
    assume(c > 2);
    *cp1 = c;
    escapeToMemory(cp1);
    SEA_DIE(cp1);
    SEA_WRITE_CACHE(b, *b);
  }
  SEA_DIE(b);
  char r;
  SEA_READ_CACHE(r, p);
  sassert(r == 0 || r > 2);
  SEA_DIE(p);
  return 0;
}
