#include "memcex.h"

// writing and reading primitive field of a nondet pointer
int main(void) {
    struct st *p;
    p = __VERIFIER_nondet_st();

    assume(p > 0);
    BASE_PTR(p);
    p->y = 43;
    if (p->x == 42 && p->y == 43) {
        __VERIFIER_error();
    }
    return 0;
}
