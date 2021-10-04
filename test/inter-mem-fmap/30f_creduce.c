// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 --no-lower-gv-init-structs %s
// CHECK: ^sat$

void __VERIFIER_error();
struct a {};
union b {
  struct a c;
  int d;
};
struct {
  union b e;
} f = {{}};
struct aa {
  void *g;
};
struct ab {
  int h;
};
struct i {
  char ac;
};
struct j {
  struct i *ae;
} * l;
int k, n;
int m(int);
int s(int);

__attribute__((noinline))
int o(struct aa *p) {
  char q;
  int a, r;
  s(r);
  l = m(a);
  p->g = l;
  if (q)
    t(f);
  u(n, s, "");
  l->ae->ac = 0;
}

__attribute__((noinline))
int v(struct aa *p) {
  struct j *w = p->g = &w;
  struct ab *b;
  b->h = o;
  __VERIFIER_error();
}

int main() {
 ak:
  v(&k);
  o(k);
  goto ak;
}

