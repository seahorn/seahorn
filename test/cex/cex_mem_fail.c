// RUN: %sea exe-cex -O0 --verify "%s" 2>&1 | OutputCheck %s
// RUN: %sea exe-cex -O0 --verify --bit-mem-precise "%s" 2>&1 | OutputCheck %s
// CHECK: ^__VERIFIER_error was not executed$

/*
 Writing and reading primitive field of a nondet pointer
*/

#include "seahorn/seahorn.h"

struct st {
    int x;
    int y;
    struct st *next;
};

extern struct st *nd_st(void);

int main(int argc, char**argv) {
    struct st *p;
    p = nd_st();

    assume(p > 0);
    p->y = 43;
    if (p->x == 42) {
      if (p->y == 43) {
        __VERIFIER_error();
      }
    }
    return 0;
}
