// RUN: sea pf -O0 --dsa=sea-cs --horn-inter-proc-mem --horn-shadow-mem-optimize=false %s
// CHECK: ^unsat$

/* #include <stdint.h> */
/* #include <stdbool.h> */
/* #include <stddef.h> */
/* #include <stdlib.h> */

/*
  This example is harder because the pointer analysis infers offset collapsed in
  main. However, this is not the case in init_list, so the transformation
  can be applied.
 */

extern void sea_dsa_alias(const void *p, ...);
extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error (), 0))

#define MAX_LIST 30

typedef struct {
  int * sz;
  int * cap;
  int data[MAX_LIST];
} List;

__attribute__((noinline))
void init_list(List * l) {

  l->sz=l->data;
  l->cap=&(l->data[MAX_LIST-1]);
}

//bounded memory written and read
__attribute__((noinline))
int push_elem(List * l, int data) {

  if(l->sz < l->cap){
    *l->sz = data;
    l->sz++;
    return 0;
  }
  return -1;
}

int main() {

  List l1, l2;

  init_list(&l1);
  init_list(&l2);

  assume(&l1 + sizeof(List) < &l2);
  sea_dsa_alias(&l1,&l2);

  push_elem(&l2, 42);

  sassert(l1.sz <= &(l1.data[MAX_LIST-1]));

  return 0;
}
