/* Diamond inheritance */

// sea inspect -O0 --log=cha test_04.cpp --cha

extern void foo(int);
extern int nd_int();

class A {
public:
  A() {}
  virtual ~A() {}
  virtual int f() { return 5; }
};

class B : virtual public A {
public:
  B() : A() {}
  virtual ~B() {}
  virtual int f() { return 10; }
};

class C : virtual public A {
public:
  C() : A() {}
  virtual ~C() {}
  virtual int f() { return 10; }
};

class D : public B, C {
public:
  D() : B(), C() {}

  virtual int f() { return nd_int(); }
};

int main(int argc, char *argv[]) {
  A *p = 0;
  if (nd_int()) {
    p = new B();
  } else if (nd_int()) {
    p = new C();
  } else {
    p = new D();
  }

  p->f();

  delete p;
  return 0;
}
