extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
__attribute__((always_inline)) void assert (int v)  { if (!v) __VERIFIER_error (); }

#define N 10

int main ()
{
  int a[N], b[N];
  int i,j;

  for (i=0;i<N;i++)
    b[i] = a[i];

  for (j=0;j<N;j++)  
    assert (a[j] != b[j]);

  return 42;
}
