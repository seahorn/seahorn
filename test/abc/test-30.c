// RUN: %sea abc -O0 --abc-encoding=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include <string.h>

struct foo {
  int x;
  int a[10];
};

extern void do_something(struct foo *);

int main() {
  struct foo f;
  int b[10];
  int i;
  for (i = 0; i < 10; i++) {
    b[i] = i;
  }
  memcpy(&(f.a), b, sizeof(int) * 10);

  do_something(&f);
  return 42;
}
