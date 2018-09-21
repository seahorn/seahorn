#include "memcex.h"

// reading non-deterministic pointer

int main(void) {
    if (__VERIFIER_nondet_ptr() > 0) {
        __VERIFIER_error();
    }
    return 0;
}
