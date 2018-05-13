#include "memcex.h"


// reading nondet pointer to a simple struct
int main(void) {
    struct st *p;
    p = nd_st();

    if (p > 0) {
        __VERIFIER_error();
    }
    return 0;
}
