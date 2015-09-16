extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
__attribute__((always_inline)) void assert  (int v)  { if (!v) __VERIFIER_error (); }

#define N 10

int a[N];

int main ()
{
  int i;

  for (i=0;i<N;i++)
    a[i] = 0;
  
  for (i=0;i<N;i++)
    assert (a[i] == 0);
  
  return 42;
}
