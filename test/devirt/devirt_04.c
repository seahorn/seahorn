// RUN: %sea pf -O1 --devirt-functions "%s"  2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

extern int nd_int(void);

int a(void);
int b(void);
int c(int *);
int d(int *);

int main(int argc, char **argv) {
  int (*p)(void);
  int (*q)(int *);

  if (nd_int()) {
    p = a;
    q = c;
  } else {
    p = b;
    q = d;
  }

  int x = p();
  int y = 5;
  int r = q(&y); // the indirect call returns an integer
  int z = 2;
  q(&z); // the indirect call returns nothing

  sassert((x + r) >= 5);
  sassert(z >= 7);
}

int a() { return 10; }
int b() { return 5; }
int c(int *x) {
  *x = *x + 5;
  return (nd_int() ? 0 : 1);
}
int d(int *x) {
  *x = *x + 10;
  return (nd_int() ? 0 : 1);
}
