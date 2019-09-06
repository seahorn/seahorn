/* Simple inheritance */

// sea inspect -O0 --log=cha test_00.cpp --cha

extern void foo(int);
extern int nd_int();

class B {
public:
  B() {}
  virtual ~B() {}
  virtual int f1() = 0;
  virtual int f2(int x) = 0;
  virtual int f3() { return 0; }
};

class D1 : public B {
public:
  D1() : B() {}

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

class D2 : public B {
  int m_x;

public:
  D2() : B(), m_x(0) {}

  virtual int f1() { return 5; }

  virtual int f2(int x) { return x + m_x + 10; }
};

int main(int argc, char *argv[]) {
  B *p = 0;
  if (nd_int()) {
    p = new D1();
  } else {
    p = new D2();
  }

  p->f1();
  p->f2(nd_int());
  p->f3();

  delete p;
  return 0;
}
