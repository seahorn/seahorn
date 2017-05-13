// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^sat$

// Used to avoid llvm to optimize away
extern void read (int);

int MAX_ARRAY = 10;

// To test loops that decrements a counter
int main(int argc, char** argv) {
  int a[MAX_ARRAY];
  int i;
  for (i = MAX_ARRAY - 1; i >= 0; i--) {
    a[i] = i;
  }
  // buffer underflow
  read(a[i]);
  // buffer overflow
  read(a[MAX_ARRAY]);
  return 0;
}
