extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
__attribute__((always_inline)) void assert  (int v)  { if (!v) __VERIFIER_error (); }

int a[10];

int main ()
{
  int i;

  for (i=0;i<10;i++)
    a[i] = 0;
  
  for (i=0;i<10;i++)
    assert (a[i] == 0);
  
  return 42;
}
