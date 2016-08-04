#include <stdlib.h>

extern void __VERIFIER_assume (int);
extern int  __VERIFIER_NONDET(void);
extern void __VERIFIER_error (void) __attribute__((noreturn)); 
void sassert (int v) { if (!v) __VERIFIER_error (); }
#define assume __VERIFIER_assume 
#define nd __VERIFIER_NONDET


/**
   DSA says that p and q cannot alias.
   Probably the nodes for p and q are incomplete.
 */

void bar (int*, int*);
int* get ();



int main ()
{
  int *p, *q;
  
  
  p = get();
  *p = 12;
 
  q = get ();
  *q = 22;
  
  bar (p, q);
  
  sassert (*q != *p);
  return 42;
}
