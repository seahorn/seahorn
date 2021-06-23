// RUN: %sea fpf --inline --horn-bv2-crab-rng --dsa=sea-cs-t --bmc=opsem --horn-vcgen-use-ite --horn-vcgen-only-dataflow=true --horn-bmc-coi=true --sea-opsem-allocator=static "%s" 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include <seahorn/seahorn.h>
#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>

/* Externalize Helper Function */
extern int nd_int(void);
extern size_t nd_size_t(void);
extern bool nd_bool();
extern void memhavoc(void *, size_t);

void check_access(size_t *ary, int len, size_t value) {
    int i = nd_size_t();
    assume(i < len);
    sassert(ary[0] == value);
    // sassert(sea_is_dereferenceable(ary, sizeof(int)));
    // sassert(sea_is_dereferenceable(ary, i));
}

void test_1(int len){
    size_t size = sizeof(int) * len;
    size_t *x = (size_t *)malloc(size);
    memhavoc(x, size);
    x[0] = 3;
    check_access(x, len, 3);
    free(x);
}

void test_2(int len){
    size_t *sptr = malloc(sizeof(size_t));
    size_t size = len * sizeof(int);
    *sptr = size;
    size_t *y = (size_t *)malloc(*sptr);
    memhavoc(y, *sptr);
    y[0] = *sptr;
    check_access(y, len, *sptr);
    free(y);
}

int main(void) {
    int x = nd_int();
    assume(x > 0);
    assume(x < 10);
    int len = nd_bool() ? 100: x;
    test_1(len);
    test_2(x);
    return 0;
}