// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

extern void __VERIFIER_error (void);

enum a { b };
struct c {
  void *d;
  void *e;
};
int *a;
void f();
int p(int);
int q();

__attribute__((noinline))
void g(int *h, char i, char *v) {
  int j, l;
  void (*k)(int *, char, char *);
  enum a m;
  long n, o;
  switch (i) {
  case 3:
    *v = l;
    k(h, 9, m);
  default:
    p(j);
    if (n)
      if (o)
        q();
  }
}

__attribute__((noinline))
void r(int *h, char i, char *v) {
  void (*s)(int *, char, char *);
  s(h, 0, 0);
  f();
}

struct c t = {g, r};
void u() { __VERIFIER_error(); }

__attribute__((noinline))
void f() {
  void *b;
  int * a = b;
}
