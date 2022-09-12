// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 --no-lower-gv-init-structs %s
// CHECK: ^sat$

// This is a test for writing the regions of recursive calls (treated as noops)

struct b {
  _Bool *c;
  void *d
};
int *e;
char am, an, ao;
void __VERIFIER_error();
int f() {
  int g;
  return g;
}
void h(j) {}
__attribute__((noinline))
void i(int *j, char k, char *q) {
  long l, o, p;
  void (*m)(int *, char, char *);
  int n;
  switch (k) {
  case 3:
    *q = n;
    m(j, 9, 0);
  default:
    h(l);
    if (o)
      if (p)
        f();
  }
}
__attribute__((noinline))
void r(int *j, char k, char *q) {
  void (*s)(int *, char, char *);
  char ag;
  long ah, ai;
  e = j;
  switch (k) {
  case 0:
    s(j, 2, ag);
  default:
    if (ah)
      if (ai)
        f();
    f();
  }
}
struct b a = {i, r};
int main() {
  char aq;
  void *ar;
  i(ar, aq, am);
  r(ar, an, ao);
  __VERIFIER_error();
}
