// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

// Used to avoid llvm to optimize away
extern void read (int);

extern int unknown ();

#define MAX_ARRAY 10

int main(int argc, char**argv) {
  int i, j;
  int a[MAX_ARRAY][MAX_ARRAY];
  for (i = 0; i < MAX_ARRAY; i++) 
  {
    for (j = 0; j < MAX_ARRAY; j++) 
    {
      a[i][j] = unknown ();
    }
  }

  for (i = 0; i < MAX_ARRAY; i++) 
  {
    read(a[i][i]);  
  }
  
  return 0;
}
