// RUN: %sea pf "%s"  2>&1 | OutputCheck %s
// CHECK: ^sat$

#include "seahorn/seahorn.h"
#define N 10

int a[N];

int main ()
{
  int i;

  for (i=0;i<N;i++)
    a[i] = 0;

  for (i=0;i<N;i++)
    sassert (a[i] == 0);

  return 42;
}
