#pragma once

#include <stdint.h>
#include <seahorn/seahorn.h>

#define USE_FIX_ADDR

#define BASE_ADDR 0xbeef0

#ifdef USE_FIX_ADDR
#define PTR(X,Y) assume(((intptr_t)X) == (BASE_ADDR + Y));
#define BASE_PTR(X) PTR(X,0)
#else
#define BASE_PTR(X) (void)
#define PTR(X,Y) (void)
#endif



extern int nd_int(void);
extern int* nd_ptr(void);

struct st {
    int x;
    int y;
    struct st *next;
};

extern struct st *nd_st(void);
