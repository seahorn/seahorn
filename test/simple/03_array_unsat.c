// RUN: %sea pf "%s"  2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

extern int nd();

#define N 100
// Different ways of initialization
struct foo {
  int a;
  int b;
  int c;
};
struct foo hh;
int a[N];
int x = 4;
int b[3] = {2, 3, 4};

int main() {
  int i;
  for (i = 0; i < N; i++) {
    if (nd())
      a[i] = b[2];
    else if (nd())
      a[i] = hh.a;
    else
      a[i] = x;
  }

  int res = a[i - 1];
  sassert(res >= 0 && res <= 5);
  return res;
}
