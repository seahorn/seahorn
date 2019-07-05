// RUN: %sea abc -O0 --abc-encoding=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

// Used to avoid llvm to optimize away
extern void read(int);

int *foo(int *c, int n, int x) {
  int i;
  for (i = 0; i < n; i++)
    c[i] = x;
  return c;
}

int main() {
  int a[10];
  /*int *b =*/foo(a, 10, 5);
  int b[10];
  int *c = foo(b, 10, 7);
  read(c[7]);
  return 0;
}
