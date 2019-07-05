// RUN: %sea abc -O0 --abc-encoding=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^sat$

int x = 6;

struct foo {
  int x;
  int y;
};

int B[10];

int main(int argc, char **argv) {
  int A[5];

  struct foo a;
  a.x = 59;
  x++;
  B[8] = 23;
  int z = x + 7 + a.y + A[4] + B[10];
  return z;
}
