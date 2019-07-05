// RUN: %sea abc -O0 --abc-encoding=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^sat$

extern int nd();
extern void __VERIFIER_assume(int v);
#define assume __VERIFIER_assume

// Used to avoid llvm to optimize away
extern void read(int);

extern void *malloc(unsigned int);

// To test loops
int main(int argc, char **argv) {
  int i;

  int n = nd();
  assume(n > 0);
  int *a = (int *)malloc(sizeof(int) * n);

  int *p;
  p = a;
  for (i = 0; i < n; i++) {
    p[i] = i;
  }
  // trick llvm so that it cannot detect overflow
  read(p[(nd() > 0 ? i - 1 : i)]);
  return 0;
}
