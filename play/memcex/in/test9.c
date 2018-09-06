#include "memcex.h"

// two overlapping non-deterministic structs
int main(void) {
    struct st *p;
    struct st *q;
    p = __VERIFIER_nondet_st();
    q = __VERIFIER_nondet_st();

    struct st *z;
    if (p > 0) {
        z = p;
    }
    else {
        z = q;
    }
    assume(z > 0);
    BASE_PTR(p);
    assume(q>0);

    if (p->x == 10 && q->x == 10) {
        p->x = 55;
        if (q->x == 55) {
            // reachable when p == q, which is possible since __VERIFIER_nondet_st()
            // does not guarantee to return unique addresses
            __VERIFIER_error();
        }
    }
    return 0;
}
