#include <stdlib.h>

extern void __VERIFIER_assume (int);
extern int  __VERIFIER_NONDET(void);
extern void __VERIFIER_error (void) __attribute__((noreturn)); 
void sassert (int v) { if (!v) __VERIFIER_error (); }
#define assume __VERIFIER_assume 
#define nd __VERIFIER_NONDET


int nd ();
void bar (int*, int*);
int *g;

int *get ()
{
  if (g == NULL)
    g = (int*) malloc (sizeof (int));
  return g;
}

int main ()
{
  int *p, *q;
  
  
  p = get();
  *p = 12;
 
  q = get ();
  *q = 22;

  if (nd ())
  {
    q = get ();
    *q = 33;
  }
  
  bar (p, q);

  sassert (*q != *p);
}
