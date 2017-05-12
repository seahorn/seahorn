// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include <stdio.h>
int main(int argc, char**argv) 
{
  int i,j;
  int a[10];
  int b[4];
  for (i = 0; i < 10; i++) 
  {
    a[i] = 444;
  }
  for (j = 0; j < 4; j++) 
  {
    b[j] = 777;
  }

  printf("%d\n", a[i-1] + b[j-1]);
  return 42;
}
