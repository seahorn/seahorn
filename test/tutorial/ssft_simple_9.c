// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// CHECK: ^unsat$

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
