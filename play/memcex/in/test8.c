#include "memcex.h"

// Failed attempt to create a circular linked list
// Fails because p is assumed to not alias p->next

int main(void) {
    struct st *p;
    p = __VERIFIER_nondet_st();

    assume(p > 0);
    BASE_PTR(p);

    if (p->x == 42) {
        if (p->next != 0) {
            p->next->y = 0;
            p->y = 474;
            if (p->next->x == 526) {
                if (p->next->x + p->next->y == 1000) {
                    __VERIFIER_error();
                }
            }
        }
    }
    return 0;
}
