// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include <stdio.h>
#include <stdlib.h>

int bar(int *a, int sz) 
{
  int i;
  for (i = 0; i < sz; i++) 
  {
    a[i] = i;
  }
  printf("%d\n", a[i-1]);
  return 42;
}

int foo(int sz) 
{
  int * a = (int*) malloc(sizeof(int) * sz);
  return bar (a, sz);
}


int main(int argc, char**argv) 
{
  return foo(10);
}
