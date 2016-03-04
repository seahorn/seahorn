// SAFE

extern int nd ();
extern void __VERIFIER_assume (int v);
#define assume __VERIFIER_assume

#include <stdio.h>
#include <stdlib.h>

// To test loops 
int main(int argc, char**argv) 
{
  int i;

  int n = nd ();
  assume (n > 0);
  int * a = (int*) malloc(sizeof(int) * n);

  int *p;
  p = a;
  for (i = 0; i < n; i++) 
  {
    p[i] = i;
  }

  printf("%d\n", p[i]);
  return 42;
}
