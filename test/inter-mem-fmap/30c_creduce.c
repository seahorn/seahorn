// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^sat$

char a;
void __VERIFIER_error();

__attribute__((noinline))
void b(struct c *d, int e) {
  long f;
  char *g;
  void *h;
  g = d;
  *g = a;
  if (e)
    memcpy(d, h, f);
}
void i() { __VERIFIER_error(); }


