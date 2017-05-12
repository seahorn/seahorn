// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^sat$

#include <stdio.h>

extern int nd ();

int a[10];

// To test loops 
int main(int argc, char**argv) 
{
  int i;

  for (i = 0; i < 10; i++) {
    a[i] = i;
  }
  // trick llvm so that it cannot detect overflow
  printf("%d\n", a[(nd()>0?i-1:i)]);
  return 42;
}
