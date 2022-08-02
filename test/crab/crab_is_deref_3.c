// RUN: %sea -O3 fpcf --inline --seapp-crab-lower-is-deref --seapp-crab-dom=zones --seapp-crab-stats=true --dsa=sea-cs-t --bmc=opsem --horn-vcgen-use-ite --horn-vcgen-only-dataflow=false --horn-bmc-coi=false --horn-stats=true --sea-opsem-allocator=static "%s" 2>&1 | OutputCheck %s
// CHECK: crab.pp.isderef.solve 4

#include <seahorn/seahorn.h>
#include <stdio.h>
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>

extern int nd_int(void);
extern bool nd_bool(void);
extern void memhavoc(void *, size_t);

// Domain: zones
int main() {
    int len = nd_int();
    assume(len > 0);
    uint8_t *ptr = malloc(len);
    sassert(sea_is_dereferenceable(ptr, len));
    for (int j = 1; j < len; ++j) {
      uint8_t *p_j = ptr + j;
      sassert(sea_is_dereferenceable(p_j, 1));
      int i = j - 1;
      while (i >= 0) {
        uint8_t *p_i = ptr + i;
        sassert(sea_is_dereferenceable(p_i, 1));
        sassert(sea_is_dereferenceable(p_i + 1, 1));
        -- i;
      }
    }
   return 0;
}
