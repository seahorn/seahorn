extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
__attribute__((always_inline)) void assert  (int v)  { if (!v) __VERIFIER_error (); }

extern int nd ();

#define N 1000
// Different ways of initialization
struct foo { int a; int b; int c;}; struct foo hh;
int a[N];
int x = 4;
int b [3] = {2, 3, 4};

int main ()
{
  int i;
  for (i=0;i<N;i++)
  {
    if (nd ())
      a[i] = b[2];
    else if (nd ())
      a[i] = hh.a;
    else
      a[i] = x;
  }

  int res = a[i-1];
  assert (res >= 0 && res <= 5);
  return res;
}
