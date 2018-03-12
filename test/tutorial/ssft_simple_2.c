// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// CHECK: ^unsat$

int unknown(void);

extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
void assert (int v) { if (!v) __VERIFIER_error (); }

#define static_assert assert

int main(void)
{
 int k=1;
 int i=1;
 int j;
 int n = unknown();
 while(i<n) {
  j=0;
  while(j<i) {
      k += (i-j);
      j++;
  }
  i++;
 }
 static_assert(k>=n);
return 0;
}

