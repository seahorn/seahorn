/* Multiple inheritance */

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

class B {
 public:
  B() {}
  virtual ~B(){}
  virtual int g() { return 10;}
};

class C: public A, B{
 public:

  C(): A(), B() {}

  virtual int f() { return 15; }
  virtual int g() { return 20; }
};

class D: public C {
 public:

  D(): C() {}

  virtual int f() { return 20; }
  virtual int g() { return 30; }
};


int main(int argc, char* argv[]) {
  C* p = 0;
  if (nd_int()) {
    p = new C();
  } else {
    p = new D();    
  }
  
  int r1 = p->f();
  int r2 = p->g();
  delete p;
  
  sassert(r1 >= 5 && r1 <= 20);
  sassert(r2 >= 10 && r2 <= 30);  

  // With -O0 these calls are indirect calls.
  // With -O3 they are direct calls.
  C* q = new C();
  int r3 = q->f();
  int r4 = q->g();
  delete q;

  sassert(r3 >= 5 && r3 <= 20);
  sassert(r4 >= 10 && r4 <= 30);  

  return 0;
}
