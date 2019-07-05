// RUN: %sea abc -O0 --abc-encoding=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^sat$

extern int nd();

// Used to avoid llvm to optimize away
extern void read(int);

extern void *malloc(unsigned int);

int bar(int *a, int sz) {
  int i;
  for (i = 0; i < sz; i++) {
    a[i] = i;
  }
  // trick llvm so that it cannot detect overflow
  read(a[(nd() > 0 ? i - 1 : i)]);
  return 0;
}

int foo(int sz) {
  int *a = (int *)malloc(sizeof(int) * sz);
  return bar(a, sz);
}

int main(int argc, char **argv) { return foo(10); }
