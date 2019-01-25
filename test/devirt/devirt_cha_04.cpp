/* Diamond inheritance */

// RUN: %sea pf -O0 --devirt-functions-with-cha "%s"  2>&1 | OutputCheck %s
// RUN: %sea pf -O3 --devirt-functions-with-cha "%s"  2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

extern void foo(int);
extern int nd_int();

class A {
 public:
  A() {}
  virtual ~A(){}
  virtual int f() { return 5;} 
};

class B: virtual public A {
 public:
  B(): A()  {}
  virtual ~B(){}
  virtual int f() { return 10;}
};

class C: virtual public A {
 public:
  C(): A()  {}
  virtual ~C(){}
  virtual int f() { return 15;}
};

class D: public B, public C {
 public:

  D(): B(), C() {}

  virtual int f() { return 20; }
};


int main(int argc, char* argv[]) {
  A* p = 0;
  if (nd_int()) {
    p = new B();
  } else if (nd_int()) {
    p = new C();    
  } else {
    p = new D();
  }
  
  int r1 = p->f();
  delete p;
  sassert(r1 >= 5 && r1 <= 20);

  C* q = 0;
  if (nd_int()) {
    q = new C();
  } else {
    q = new D();
  }

  int r2 = q->f();
  delete q;
  sassert(r2 >= 15 && r2 <= 20);
  return 0;
}
