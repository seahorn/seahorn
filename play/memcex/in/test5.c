#include "memcex.h"

// reading a pointer field of a struct
int main(void) {
    struct st *p;
    p = __VERIFIER_nondet_st();

    assume(p > 0);
    BASE_PTR(p);

    if (p->x == 42) {
        if (p->next != 0) {
            PTR(p->next, sizeof(struct st));
            __VERIFIER_error();
        }
    }
    return 0;
}
