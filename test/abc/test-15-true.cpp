// RUN: %sea pf -O3 --lower-invoke --symbolize-constant-loop-bounds --simplify-pointer-loops --abc=%abc_encoding %dsa --abc-escape-ptr "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

extern "C" int nd ();
extern "C" void __VERIFIER_assume (int);
#define assume __VERIFIER_assume

struct foo {
  int x;
  foo (): x(0) { }  

  void set (int a){
    x = a;
  }
};

struct bar {
  foo * _list;
  int _n;
  bar (int n): _list(0), _n (n) {
    _list = new foo [_n];    
  }

  void update (int i, int x) {
    //_list [i].x = x;
    _list [i].set (x);
  }

  ~bar () { delete [] _list; }
};
  

int main (){
  int n = nd ();
  assume (n > 0);

  bar l (n);
  for (int i=0; i<l._n;i++) {
    l.update (i, 8);
  } 
  return 0;
}
