// RUN: %sea pf -O3 --devirt-functions --lower-invoke --symbolize-constant-loop-bounds --simplify-pointer-loops --abc=%abc_encoding %dsa --abc-escape-ptr --abc-use-deref --abc-disable-underflow "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$


#define N 10

typedef int field_t;

struct A {
  field_t _x;
  A (field_t x): _x(x) {}
};


struct B: public A {
  field_t _y;
  B (field_t x, field_t y): A(x), _y(y) {}
};

struct C: public A {
  field_t _z; field_t _w;
  C (field_t x, field_t z, field_t w): A(x), _z(z), _w(w){}
};


extern int nd ();
A* p[N];

A* foo () {
  A* last = 0;
  for (int i=0; i < N; i++) {
    if (nd ()) {
      B* b= new B (3*i, 4*i);
      p[i] = b;
      #ifdef LAST
      last = b;
      #endif
    }
    else {
      C* c= new C (2*i, 3*i, 4*i);
      p[i] = c;
      #ifdef LAST
      last = c;
      #endif
    }
  }
  return last;
}

int main (int argc, char**argv) {
  A* last = foo ();
  //B* q = (B *) p[2];
  //return q->_y;

  field_t res;
  if (nd ()) {
    B* b = (B *) p[2];
    #ifdef LAST
    res = b->_y + last->_x;
    #else
    res = b->_y;
    #endif 
  }
  else {
    C* c = (C *) p[2];
    #ifdef LAST
    res = c->_z + last->_x;
    #else
    res = c->_z; 
    #endif 
    // UNSAFE
    //res = c->_w ;
  }
  return res;
  
}

