// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^sat$

extern int nd ();

#include <stdio.h>
#include <stdlib.h>

int bar(int *a, int sz) 
{
  int i;
  for (i = 0; i < sz; i++) 
  {
    a[i] = i;
  }
  // trick llvm so that it cannot detect overflow
  printf("%d\n", a[(nd () > 0 ? i-1 : i)]);
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
