#include <stdlib.h>

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
  
  if (*q == *p) return 42;
  
 UFO: goto UFO;
}
