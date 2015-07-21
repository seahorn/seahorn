extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
void assert (int v) { if (!v) __VERIFIER_error (); }

extern int nd ();

int main ()
{
  int a[1000], b[1000];
  int i;
  int c = nd ();
  for (i=0;i<1000;i++)
  {
    if (c)
      a[i] = 0;
    else 
      a[i] = 5;

    if (c)
      b[i] = 0;
    else 
      b[i] =5;

  }

  for (i=0;i<1000;i++)  
    assert (a[i] == b[i]);

  return 42;
}
