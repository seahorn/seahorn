// RUN: %sea clang -m64 -S -o /tmp/bitcode.bc %s > /dev/null 2>&1
// RUN: %seapp -fat-bnd-check -S -o /tmp/bitcode.fat.bc /tmp/bitcode.bc > /dev/null 2>&1 
// RUN: clang++ /tmp/bitcode.fat.bc %libsea-rt -o /tmp/cex.exe > /dev/null 2>&1
// RUN: /tmp/cex.exe 2>&1 | OutputCheck %s


// CHECK-L: [sea] __VERIFIER_error was executed
// XFAIL: *

#include "seahorn/seahorn.h"
#include <stddef.h>
#include <stdlib.h>

typedef struct bounded_array {
    void* arr;
    size_t len;
} bar_t;

int main(void) {
    char base_a[] = "aaaaa";
    bar_t bar_a = {
      .arr = base_a,
      .len = sizeof(base_a) / sizeof(*base_a)
    };
    ((char*)bar_a.arr)[bar_a.len] = 'd';
    return 0;
}

