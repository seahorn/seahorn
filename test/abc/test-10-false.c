// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^sat$

#include <stdio.h>
int main(int argc, char**argv) 
{
  int i,j;

  int b[4];
  int a[10];
  
  for (i = 0; i < 10; i++) 
  {
    a[i] = 444;
  }

  for (j = 0; j < 4; j++) 
  {
    b[j+1] = 777;
  }

  printf("%d\n", a[i-1] + b[j-1]);
  return 42;
}
