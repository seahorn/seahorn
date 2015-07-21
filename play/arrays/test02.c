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

  int j = nd ();
  if (j >=0 && j < 1000)
    assert (a[j] >= 0 && a[j] <= 5);
  return 42;
}
