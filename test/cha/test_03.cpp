/* Multiple inheritance */

// sea inspect -O0 --log=cha test_03.cpp --cha

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

  virtual int f() { return 20; }
  virtual int g() { return 30; }
};

class D: public C {
 public:

  D(): C() {}

  virtual int f() { return nd_int(); }
  virtual int g() { return nd_int(); }
};


int main(int argc, char* argv[]) {
  C* p = 0;
  if (nd_int()) {
    p = new C();
  } else {
    p = new D();    
  }
  
  p->f();
  p->g();  

  delete p;
  return 0;
}
