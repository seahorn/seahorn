// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

int e, f = -1;
void __VERIFIER_error();
void a();
void b() {
  int c;
  if (c)
    a();
}
int main(void) {
 d:
  b();
  b();
  goto d;
}

__attribute__((noinline))
void g() {
  if (e)
    f = 0;
  if (f != -1)
    e = e - 1;
}
__attribute__((noinline))
void a() {
  if (e < 5)
    e = e + 1;
  g();
  int h = e == 0;
  if (h)
    ;
  else
    __VERIFIER_error();
}
