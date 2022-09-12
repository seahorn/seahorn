// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 --no-lower-gv-init-structs %s
// CHECK: ^sat$

// the option --lower-gv-init-struct=false in seahorn is needed in this example
// (storing in structs is not supported)

struct a d;
void __VERIFIER_error();
struct a {
  int *b;
} c() {
  __VERIFIER_error();
  }
void e();
void f() { e(&d); }
struct a d = {f};
