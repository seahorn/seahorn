#include "memcex.h"

// reading a primitive field of a struct
int main(void) {
    struct st *p;
    p = __VERIFIER_nondet_st();

    assume(p > 0);
    BASE_PTR(p);
    if (p->x == 42) {
        __VERIFIER_error();
    }
    return 0;
}
