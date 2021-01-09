// RUN: %solve --horn-bmc-engine=mono --horn-bv2-extra-widemem --horn-bv2-lambdas=false --horn-bmc --horn-bv2=true --keep-shadows=true --cex=/tmp/test_cex_mem.ll %s > /dev/null 2>&1
// RUN: %cex --run -g %s /tmp/test_cex_mem.ll 2>&1 | OutputCheck %s


// CHECK: ^__VERIFIER_error was executed$
/*
 Writing and reading primitive field of a nondet pointer
*/
#include <stddef.h>
#include <stdlib.h>
#include "seahorn/seahorn.h"

struct st {
    int x;
    int y;
    struct st *next;
};

extern struct st *nd_st(void);
extern void memhavoc(void *ptr, size_t size);

int main(int argc, char**argv) {
    struct st *p = malloc(sizeof(struct st));
    memhavoc(p, sizeof(struct st));

    assume(p > 0);
    p->y = 43;
    if (p->x == 42) {
      if (p->y == 43) {
        __VERIFIER_error();
      }
    }
    free(p);
    return 0;
}
