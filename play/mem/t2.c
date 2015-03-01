#include <stdlib.h>

// DSA knows that p and q might alias in main

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
  
  bar (p, q);
  
  if (*q == *p) return 42;
  
 UFO: goto UFO;
}
