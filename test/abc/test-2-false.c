// RUN: %sea abc -O0 --abc-encoding=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^sat$

// Used to avoid llvm to optimize away
extern void read(int);

extern int nd();

int main(int argc, char **argv) {
  int i;
  int a[10];
  for (i = 0; i < 10; i++) {
    a[i + 1] = 9999;
  }

  // trick llvm so that it cannot detect overflow
  read(a[(nd() > 0 ? i - 1 : i)]);
  return 0;
}
