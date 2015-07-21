extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
void assert (int v) { if (!v) __VERIFIER_error (); }

extern int nd ();

int main ()
{
  int a[1000];
  int i;
  for (i=0;i<1000;i++)
  {
    if (nd ())
      a[i] = 0;
    else 
      a[i] =5;
  }

  for (i=0;i<1000;i++)  
    assert (a[i] >= 0 && a[i] <= 10);

  return 42;
}
