// SAFE

extern int unknown ();

#include <stdio.h>
#include <stdlib.h>

// To test loops 
int main(int argc, char**argv) 
{
  int i;

  int * a = (int*) malloc(sizeof(int) * 10);
  int *p;
  p = a;
  for (i = 0; i < 10; i++) 
  {
    p[i] = i;
  }

  printf("%d\n", p[i-1]);
  return 42;
}
