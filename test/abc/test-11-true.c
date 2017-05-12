// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include <stdio.h>

int foo(int k, int N) {
  return k + N;
}

int bar(int p) {
  return p + foo(p, 10);
}

int main(int argc, char** argv) {
  int a[56];
  int x = foo(5, 10); // x=15
  int y = x + bar(x); // y=55
  return a[y];
}
