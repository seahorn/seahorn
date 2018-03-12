// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// CHECK: ^unsat$

int unknown(void);

extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
void assert (int v) { if (!v) __VERIFIER_error (); }


#define static_assert assert

/*
 * InvGen, CAV'09 paper, fig 2
 */

int main(void) {
  int x= 0;
  int n = unknown();
  while(x<n) {
    x++;
  }
  if(n>0) static_assert(x==n);
}
