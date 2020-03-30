// RUN: sea pf -O0 --dsa=sea-cs --max-depth=10 --horn-shadow-mem-optimize=false %s
// CHECK: ^unknown$
// XFAIL: *
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
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

List * new_list() {
  List * l = (List *) malloc(sizeof(List));

  l->cap=MAX_LIST;
  l->sz=0;
  l->e=NULL;

  return l;
}

void init_list(List * l) {
  l->cap=MAX_LIST;
  l->sz=0;
  l->e=NULL;
}

//bounded memory written and read
int push_elem(List * l, int data) {

  if(l->sz < l->cap){
    LElem * e = (LElem *) malloc(sizeof(LElem));
    e->data=data;
    e->next = l->e;
    l->e = e;
    l->sz++;
    return 0;
  }
  return -1;
}

/*
  converges if l1 and l2 do not alias.
 */
int main() {
  List l1, l2;

  init_list(&l1);
  init_list(&l2);

  sea_dsa_alias(&l1,&l2); // comment this line to converge
  assume(&l1 + sizeof(List) + 100 < &l2);

  push_elem(&l2, 42);

  sassert(l1.sz <= l1.cap);

  return 0;
}
