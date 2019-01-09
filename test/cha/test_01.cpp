/* Simple inheritance but transitive closure is needed */

// sea inspect -O0 --log=cha test_01.cpp --cha

extern void foo(int);
extern int nd_int();

class B {
 public:
  B() {}
  virtual ~B(){}
  virtual int f1() = 0;
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
    return x + m_x + 10;
  }  
};

class D3: public D2 {
  int m_x;
 public:
  D3(): D2(), m_x(0) {}
  
  virtual int f1() {
    return 6;
  }
  
  virtual int f2(int x)  {
    return x + m_x + 11;
  }  
};

class D4: public D3 {
  int m_x;
 public:
  D4(): D3(), m_x(0) {}
  
  virtual int f1() {
    return 7;
  }
  
  virtual int f2(int x)  {
    return x + m_x + 12;
  }  
};


int main(int argc, char* argv[]) {
  B* p = 0;
  if (nd_int()) {
    p = new D3();
  } else {
    p = new D4();    
  }
  
  p->f1();
  p->f2(nd_int());  

  delete p;
  return 0;
}
