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

  int res = a[i-1];
  assert (res >= 0 && res <= 5);
  return res;
}
