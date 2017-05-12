// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include <stdio.h>

int a[10];

// To test loops 
int main(int argc, char**argv) 
{
  int i;

  for (i = 0; i < 10; i++) {
    a[i] = i;
  }
  printf("%d\n", a[i-1]);
  return 42;
}
