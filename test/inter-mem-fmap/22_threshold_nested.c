// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

#include <stdlib.h>

extern void sea_dsa_alias(const void *p, ...);
extern int nd_int();
extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error (), 0))

#define MAX_LIST 30

typedef struct LElem {
  int data;
  struct LElem * next;
} LElem;

typedef struct List {
  int cap;
  int sz;
  LElem * e;
} List;


__attribute__((noinline))
void init_list1(List * l) {
  l->cap=MAX_LIST;
}

__attribute__((noinline))
void init_list2(List * l) {
  l->cap=MAX_LIST;
  l->sz=0;
}

__attribute__((noinline))
void init_list3(List * l) {
  l->cap=MAX_LIST;
  l->sz=0;
  l->e=NULL;
}


/*
  converges if l1 and l2 do not alias.
 */
int main() {
  List l1;

  init_list1(&l1);
  init_list2(&l1);
  init_list3(&l1);

  sassert(l1.sz <= l1.cap);

  return 0;
}
