extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
 __attribute__((always_inline)) void assert (int v) { if (!v) __VERIFIER_error (); }

extern int nd ();

#define N 1000

// If ikos uses array smashing we cannot infer that a[i] = b[i] even
// if we use a relational domain. The reasons why is that array
// smashing infers actually a[i] >= 0 && a[i] <= 5 && b[i] >= 0 &&
// b[i] <= 5

int a[N];
int b[N];

int main ()
{
  int i;
  for (i=0;i<N;i++)
  {
      a[i] = 5;
      b[i] = a[i];
  }

  for (i=0;i<N;i++)  
    assert (a[i] == b[i]);

  return 42;
}
