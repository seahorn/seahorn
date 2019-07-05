// RUN: %sea pf -O0 --devirt-functions "%s"  2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

extern int nd_int(void);

int a(void);
int b(void);
int c(int);
int d(int);

int main(int argc, char **argv) {
  int (*p)(void);
  int (*q)(int);

  if (nd_int()) {
    p = a;
    q = c;
  } else {
    p = b;
    q = d;
  }

  int x = p();
  int y = q(2);

  sassert(x >= 5);
  sassert(y >= 7);

  return 0;
}

int a() { return 10; }
int b() { return 5; }
int c(int x) { return x + 5; }
int d(int x) { return x + 10; }
