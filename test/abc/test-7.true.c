// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include <stdio.h>

extern int unknown (); 

#define MAX_ARRAY 10
struct bar{
  int x;
  float y;
};

struct foo { 
  int x ; 
  struct bar y;
  int a[MAX_ARRAY][MAX_ARRAY][MAX_ARRAY-1];
};

int main(int argc, char**argv) 
{
  int i, j, k;
  struct foo x;
  for (i = 0; i < MAX_ARRAY; i++) {
    for (j = 0; j < MAX_ARRAY; j++) {
      for (k = 0; k < MAX_ARRAY -1 ; k++) {
        x.a[i][j][k] = unknown (); 
        x.y.x = x.a[i][j][k];
      }
    }
  }

  for (i = 0; i < MAX_ARRAY; i++) 
  {
    printf("%d\n",x.a[i][i][i-1]);  
  }
  
  return 42;
}
