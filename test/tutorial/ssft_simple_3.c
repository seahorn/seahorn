// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// CHECK: ^unsat$

/* requires --enable-indvar */
int unknown(void);

extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
void assert (int v) { if (!v) __VERIFIER_error (); }
#define assume __VERIFIER_assume
#define static_assert assert

/*
 * Adapted from ex17.c in NECLA test suite
 */

#ifndef BND
#define BND 100
#endif

int main(void) {
   int b;
   int j = 0;
   int flag = unknown();

   for (b=0; b < BND; ++b){
      if (flag)
         j = j +1;
   }


   if(flag)
     static_assert(j==BND);

   return 0;
}
