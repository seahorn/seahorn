// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// CHECK: ^sat$
// CHECK-NEXT: ^\[sea\] __VERIFIER_error was executed$

# define sassert(X) if(!(X)) __VERIFIER_error ()
extern int unknown1(void);

 int main(void) {
 int x=1; int y=1;
 while(unknown1()) {
   int t1 = x;
   int t2 = y;
   x = t1+ t2;
   y = t1 + t2;
  }
   sassert(y < 1);
   return 0;
 }
