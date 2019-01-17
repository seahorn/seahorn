// RUN: %sea pf -O0 --devirt-functions "%s"  2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

int a (void);
int b (void);
int c (void);
int d (void);

int main(int argc, char** argv) {
  int (*p) (void);
  int (*q) (void);  
  
  if (argc == 1) {
      p = a;
      q = c;
  } else {
      p = b;
      q = d;
  }

  int x = p();
  int y = q();

  sassert(x>= 5);
  sassert(y>= 5);    

  // If we resolve based only on types then we cannot prove this one.
  // Using aliasing we should be able to prove it.
  //sassert(y>= 15);      
  return 0;
}

int a() {return 10;}
int b() {return 5;}
int c() {return 15;}
int d() {return 20;}
