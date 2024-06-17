//; RUN: %sea "%s" --own-sem 2>&1 | OutputCheck %s
// CHECK: ^unsat$
#include "seahorn/seahorn.h"
#include <stdlib.h>

extern char *sea_begin_unique(char *);
extern char *sea_end_unique(char *);
extern char nd_char();

int main() {
  sea_tracking_on();
  char *a = malloc(1024);
  SEA_BEGIN_UNIQUE(a);
  *a = nd_char();
  assume(*a < 5);
  SEA_END_UNIQUE(a);
  sassert(*a < 5);
  return 0;
}
