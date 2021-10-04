// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

int b;
void __VERIFIER_error();
static void a() { __VERIFIER_error(); }

static void c() { b = 1; }

__attribute__((noinline))
static void d() {
  while (1)
    if (b)
      ;
    else
      break;
}

void e() {
  void *f;
  if (f)
    c();
  d;
  a;
}
