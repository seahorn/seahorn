#include <stdlib.h>

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
  
  if (*q == *p) return 42;
  
 UFO: goto UFO;
}
