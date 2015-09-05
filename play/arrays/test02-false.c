extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
 __attribute__((always_inline)) void assert (int v) { if (!v) __VERIFIER_error (); }

extern int nd ();

#define N 10
int a[N];

int main ()
{
  int i;
  for (i=0;i<N;i++)
  {
    if (nd ())
      a[i] = 0;
    else 
      a[i] =5;
  }

  int j = nd ();
  if (j >=0 && j < N)
    assert (a[j] >= 0 && a[j] <= 4);
  return 42;
}
