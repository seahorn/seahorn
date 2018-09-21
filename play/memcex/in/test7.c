#include "memcex.h"

// reading and writing through a pointer field
int main(void) {
    struct st *p;
    p = __VERIFIER_nondet_st();

    assume(p > 0);
    BASE_PTR(p);

    if (p->x == 42) {
        if (p->next != 0) {
            PTR(p->next, sizeof(struct st));
            p->next->y = 474;
            if (p->next->x == 526) {
                if (p->next->x + p->next->y == 1000) {
                    __VERIFIER_error();
                }
            }
        }
    }
    return 0;
}
