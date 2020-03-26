// RUN: %sea abc -O3 --devirt-functions --abc-surface-only  --lower-invoke --symbolize-constant-loop-bounds --simplify-pointer-loops --abc-encoding=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#define N 10

typedef char field_t;

struct A {
  field_t _x;
  A(field_t x) : _x(x) {}
};

struct B : public A {
  field_t _y;
  B(field_t x, field_t y) : A(x), _y(y) {}
};

struct C : public A {
  field_t _z;
  C(field_t x, field_t z) : A(x), _z(z) {}
};

extern int nd();
A *p[N];

void foo() {
  for (int i = 0; i < N; i++) {
    if (nd())
      p[i] = new B(3 * i, 3 * i);
    else
      p[i] = new C(5 * i, 5 * i);
  }
}

int main(int argc, char **argv) {
  foo();
  B *q = (B *)p[2];
  return q->_y;
}
