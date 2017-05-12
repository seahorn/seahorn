// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

// See how we treat global variables, struct and one-dimensional arrays
// The program is safe in terms of buffer overflow although A is
// uninitialized. B is initialized since it is a global array.
int x=6;

struct foo { 
  int x ; 
  int y;
};

int B[10];

int main(int argc, char **argv){
  int A[5];
  
  struct foo a;
  a.x = 59;
  x++;
  B[8] = 23;
  int z = x + 7 + a.y + A[4] + B[9];
  return z;
}
