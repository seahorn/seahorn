// RUN: %sea pf -O0  --dsa=sea-cs --horn-global-constraints=true --horn-singleton-aliases=true "%s" 2>&1 | OutputCheck %s
// CHECK: ^sat$
#include <seahorn/seahorn.h>

int x = 0;
int y = 0;
void inc_x () { x++; }

extern int nd(void);

int main(void)
{
  int *p;

  p = nd() ? &x : &y;
  *p = 1;
  inc_x ();
  sassert (x < 2);
  
  return 0;
}
