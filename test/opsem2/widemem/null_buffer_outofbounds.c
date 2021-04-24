//; RUN: %sea "%s" --horn-bv2-extra-widemem 2>&1 | OutputCheck %s
//; RUN: %sea "%s" --horn-bv2-widemem 2>&1 | OutputCheck %s
// CHECK: ^sat$

#include <stdlib.h>
#include <seahorn/seahorn.h>
extern int nd();
int main(void) {
    int x = 10;
    int *p;
    p = nd() ? NULL : &x;
    sassert(sea_is_dereferenceable(p, 4));
    return 0;
}

