#include<stdio.h>

//extern void __VERIFIER_assume (int);

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
__attribute__((always_inline)) void assert (int v) { if (!v) __VERIFIER_error (); }


extern int nd();
int *p, *q;
extern int* pnd();
int main ()
{
  int a = nd ();
  int y=0;

  p = pnd ();
  q = pnd ();

  while (nd()>0) {
    y++;

    //if ( (NULL==p && NULL==q)
    //     || *p==*q)
    // with expanded short circuit execution.
    if (NULL!=p) {
      goto X;
    }
    if (NULL!=q) {
      printf("Inconsistent");
      goto X;
    } 
    goto Y;
    X: // then block
    //assert(NULL!=q);
    assert(NULL!=p);
    if (*p==*q) return 1;
    Y: // else block
    printf("OLA\n");
  }


  return 42;

}
