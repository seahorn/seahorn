/* Simple inheritance but class hierarch graph will be imprecise
   because edge from D2 to D3 */

// RUN: %sea pf -O0 --devirt-functions-with-cha "%s"  2>&1 | OutputCheck %s
// CHECK: ^sat$

#include "seahorn/seahorn.h"

extern void foo(int);
extern int nd_int();

class B {
 public:
  B() {}
  virtual ~B(){}
  // virtual but not pure
  virtual int f1() { return 0; }
  // pure virtual method
  virtual int f2(int x) = 0;
};


class D1: public B{
 public:

  D1(): B() {}

  virtual int f1() {
    int x = 0;
    if (nd_int()) {
      x++;
    }
    return x;
  }
  
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
  
  virtual int f1() {
    return 5;
  }
  
  virtual int f2(int x)  {
    //return x + m_x + 10;
    return x + 10;
  }  
};

class D3: public B {
  D2 m_d; // shouldn't be part of the class hierarchy
  
 public:
  D3(): B() {}
  
  ~D3() {
  }
  
  virtual int f1() {
    // all direct calls here
    return m_d.f1() + B::f1(); 
  }
  
  virtual int f2(int x)  {
    // m_d.f2 is direct but f2 is indirect but the only possible callee is from D3.
    // This is a recursive call!
    return m_d.f2(x) + f2(x);
  }  
};


int main(int argc, char* argv[]) {
  B* p = 0;
  if (nd_int()) {
    p = new D1();
  } else if (nd_int()) {
    p = new D2();    
  } else {
    p = new D3();
  }

  // virtual call to non-pure method
  // possible callees are from classes B,D1,D2, and D3
  int r1 = p->f1();
  // virtual call to pure method
  // possible callees are from classes D1,D2, and D3
  int x = nd_int();
  int r2 = p->f2(x);  

  sassert(r1 >=0 && r1<=5);
  sassert(r2 >= x && r2 <= x+ 10);
  // another virtual call here (destructor)
  // possible callees are from classes B,D1,D2, and D3  
  delete p;
  return 0;
}
