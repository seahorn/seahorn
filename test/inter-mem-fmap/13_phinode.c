// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$


#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

extern void sea_dsa_alias(const void *p, ...);
extern int nd_int();
extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

#define MAX_LIST 30

typedef struct LElem {
  int data;
  struct LElem *next;
} LElem;

typedef struct List {
  int cap;
  int sz;
  LElem *e;
} List;

__attribute__((noinline))
void init_list(List *l) {
  l->cap = MAX_LIST;
  l->sz = 0;
  l->e = NULL;
}

// bounded memory written and read
__attribute__((noinline))
int push_elem(List *l, int data) {

  if (l->sz < l->cap) {
    LElem *e = (LElem *)malloc(sizeof(LElem));
    e->data = data;
    e->next = l->e;
    l->e = e;
    l->sz++;
    return 0;
  }
  return -1;
}

int main() {
  List l1;

  init_list(&l1);

  push_elem(&l1, 42);

  sassert(l1.sz == 1);

  return 0;
}
