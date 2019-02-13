// RUN: %shorntest %t-harness.ll %t-debug %s --max-depth=5 --enable-indvar | OutputCheck %s
// RUN: %shorntest %t-harness0.ll %t-debug0 %s --max-depth=5 -O0 --enable-indvar | OutputCheck %s
// RUN: %shorntest %t-harness1.ll %t-debug1 %s --max-depth=5 -O1 --enable-indvar | OutputCheck %s
// RUN: %shorntest %t-harness2.ll %t-debug2 %s --max-depth=5 -O2 --enable-indvar | OutputCheck %s
// RUN: %shorntest %t-harness3.ll %t-debug3 %s --max-depth=5 -O3 --enable-indvar | OutputCheck %s
// RUN: %shorntest %t-harness-.ll %t-debug- %s --max-depth=5 | OutputCheck %s --check-prefix=XFAIL_UNKNOWN
// CHECK: ^unsat$
// XFAIL_UNKNOWN: ^unknown$


/* requires --enable-indvar */

int unknown(void);

extern void __VERIFIER_error (void);
void assert (int v) { if (!v) __VERIFIER_error (); }



#define static_assert assert

int main(void) {
  int x=0;
  int y=0;
  int n = 0;
  while(unknown()) {
      x++;
      y++;
  }
  while(x!=n) {
      x--;
      y--;
  }
  static_assert(y==n);
}
