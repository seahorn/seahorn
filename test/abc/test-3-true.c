// RUN: %sea abc -O0 --abc-encoding=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

// Used to avoid llvm to optimize away
extern void read(int);

int a[10];

// To test loops
int main(int argc, char **argv) {
  int i;

  for (i = 0; i < 10; i++) {
    a[i] = i;
  }
  read(a[i - 1]);
  return 0;
}
