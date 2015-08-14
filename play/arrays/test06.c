// common pattern in real applications. 
// For instance, in the TCS module in ladee

#include <stdlib.h>

extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
__attribute__((always_inline)) void assert (int v)  { if (!v) __VERIFIER_error (); }

extern int nd ();

#define N 1000

// --- This is actually how Simulink translates the input/outputs of
//     the models to C
struct table {
  int x;
  int a[N];
};
struct table _t;
struct table * t = &_t;

int main ()
{  
  int i,j,v;

  for (i=0;i<N;i++)
    t->a[i] = 0;

  for (i=0;i<N;i++)
  {
    v = nd ();    
    if (nd () && (v >= 0 && v <= 5))
      t->a[i] = v;
  }

  for (j=0;j<N;j++)  
    assert (t->a[j] >= 0 && 
            t->a[j] <= 5);

  return 42;
}
