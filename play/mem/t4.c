#include <stdlib.h>

int x, y;
int nd();

int main ()
{
  int n = nd ();
  
  if (n) x = 4; else x = 10;
  if (n) y = 5; else y = 10;
  
  nd ();
  if (x == y) return 42;
  
 UFO: goto UFO;
}
