// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^sat$

// If the multidimensional array is global then LLVM generates a
// single GetElementPtr instruction per line

int p[2][2][2];

int main(int arg, char **argv){

  p[0][0][0] = 1;
  p[0][0][1] = 1;
  p[0][1][0] = 1;
  p[0][1][1] = 1;
  p[2][0][0] = 1;
  p[1][0][1] = 1;
  p[1][1][0] = 1;
  p[1][1][1] = 1;

  return 42;
}
