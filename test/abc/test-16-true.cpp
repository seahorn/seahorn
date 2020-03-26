/*
 * /ag/git/seahorn/build/run/bin/sea pf -O3 -g --lower-invoke  --devirt-functions  --enable-indvar --enable-loop-idiom  --abc=2 test-15-true.cpp  --show-invars --horn-global-constraints=true --horn-singleton-aliases=true --horn-make-undef-warning-error=false --abc-dsa-node=0 --abc=2 --abc-disable-underflow --track=mem --horn-stats  --verbose=1 [-DCONVERGE]
 *
 * Converges with -DCONVERGE. Diverges otherwise.
 * */

// RUN: %sea abc -O3 --lower-invoke --symbolize-constant-loop-bounds --simplify-pointer-loops --abc-encoding=%abc_encoding %dsa --abc-escape-ptr "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

extern "C" int nd();
extern "C" void __VERIFIER_assume(int);
#define assume __VERIFIER_assume

struct foo {
  int x;

#ifdef CONVERGE
  foo() {}
#else
  // Diverge
  foo() : x(0) {}
#endif
};

struct bar {
  foo *_list;
  int _n;
  bar(int n) : _list(0), _n(n) { _list = new foo[_n]; }

  void update(int i, int x) { _list[i].x = x; }

  ~bar() { delete[] _list; }
};

int main() {
  int n = nd();
  assume(n > 0);

  bar l(n);
  int i = 0;
  for (; i < l._n; i++) {
    l.update(i, 8);
  }
  return 0;
}
