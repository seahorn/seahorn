#include <stdio.h>

int * foo (int *c, int n, int x) {
  int i;
  for (i = 0; i < n; i++) 
    c[i] = x;
  return c;
}

int main() 
{
  int a[10];
  /*int *b =*/ foo (a, 10, 5);
  int b[10];
  int *c = foo (b, 10, 7);
  printf("%d\n", c[7]);
}
