/* Simple inheritance */

// RUN: %sea pf -O0 --devirt-functions-with-cha "%s"  2>&1 | OutputCheck %s
// RUN: %sea pf -O3 --devirt-functions-with-cha "%s"  2>&1 | OutputCheck %s
// CHECK: ^sat$

#include "seahorn/seahorn.h"


extern void foo(int);
extern int nd_int();

int a (void);
int b (int);

class B {
 public:
  B() {}
  virtual ~B(){}
  virtual int f1() = 0;
  virtual int f2(int x) = 0;
  virtual int f3() { return 1;}
  
};


class D1: public B{
 public:

  D1(): B() {}

  // res = [0,1]
  virtual int f1() {
    int x = 0;
    if (nd_int()) {
      x++;
    }
    return x;
  }

  // res >= x and res <= x+1
  virtual int f2(int x) {
    if (nd_int()) {
      return x++;
    } else {
      return x;
    }
  }
};


class D2: public B {
  int m_x;
 public:
  D2(): B(), m_x(0) {}

  // res = 5
  virtual int f1() {
    return 2;
  }

  // res = x + 10
  virtual int f2(int x)  {
    //return x + m_x + 10;
    return x + 10;
  }  
};


int main(int argc, char* argv[]) {
  B* p = 0;
  if (nd_int()) {
    p = new D1();
  } else {
    p = new D2();    
  }

  int r1 = p->f1();
  int x = nd_int();
  assume(x >= 0);
  int r2 = p->f2(x);
  int r3 = p->f3();

  delete p;
  
  sassert(r1 >= 0 && r1 <= 2);
  sassert(r2 >= x && r2 <= x + 5);
  sassert(r3 == 1);
  
  return 0;
}
