// RUN: %sea abc -O0 --abc-encoding=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

// Used to avoid llvm to optimize away
extern void read(int);

int main(int argc, char **argv) {
  int i, j;
  int a[10];
  int b[4];
  for (i = 0; i < 10; i++) {
    a[i] = 444;
  }
  for (j = 0; j < 4; j++) {
    b[j] = 777;
  }

  read(a[i - 1]);
  read(b[j - 1]);
  return 0;
}
