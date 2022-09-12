// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^sat$

struct a {
  void *b;
};
struct c {
  char d;
};
struct e {
  char f;
};
struct g {
  struct e h;
  struct c i;
};
void __VERIFIER_error();
void j(void);
static void k() { __VERIFIER_error(); }

__attribute__((noinline))
void l(struct a *t) {
  struct e *h;
  char a, m;
  long n, o;
  h = &((struct g *)t->b)->h;
  if (m)
    if (n)
      if (o)
        j();
  j();
  h->f = a;
}

__attribute__((noinline))
void p(struct a *t) { l(t); }

__attribute__((noinline))
void q(struct a *t) {
  {
    struct a r = *t, s = *t, d = s;
    _Bool b;
    if (b) {
      struct a c = r;
      l(&c);
    }
    if (((struct g *)s.b)->i.d)
      p(&d);
  }
  k;
}

