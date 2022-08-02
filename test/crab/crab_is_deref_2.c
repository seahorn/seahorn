// RUN: %sea -O3 fpf --inline --horn-bv2-crab-lower-is-deref --horn-bmc-crab-dom=zones --dsa=sea-cs-t --bmc=opsem --horn-vcgen-use-ite --horn-vcgen-only-dataflow=false --horn-bmc-coi=false --horn-stats=true --sea-opsem-allocator=static "%s" 2>&1 | OutputCheck %s
// RUN: %sea -O3 fpf --inline --horn-bv2-crab-check-is-deref --horn-bmc-crab-dom=zones --dsa=sea-cs-t --bmc=opsem --horn-vcgen-use-ite --horn-vcgen-only-dataflow=false --horn-bmc-coi=false --horn-stats=true --sea-opsem-allocator=static "%s" 2>&1 | OutputCheck %s
// CHECK: ^unsat$
// CHECK: crab.isderef.solve 6

#include <seahorn/seahorn.h>
#include <stdio.h>
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>

extern int nd_int(void);
extern bool nd_bool(void);
extern void memhavoc(void *, size_t);

// Domain: oct
int main() {
    int len = nd_int();
    assume(len > 0);
    int max_len = 1024;
    assume(len < max_len);
    uint8_t *ptr = malloc(len);
    sassert(sea_is_dereferenceable(ptr, len));
    while (len > 0) {
        uint8_t *p2 = ptr + (len - 1);
        sassert(sea_is_dereferenceable(p2, sizeof(uint8_t)));
        uint8_t tmp = *p2;
        -- len;
    }
   return 0;
}
