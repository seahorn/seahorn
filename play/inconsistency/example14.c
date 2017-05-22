extern int nd ();
/*
from bixie
*/

extern void __VERIFIER_error (void);
__attribute__((always_inline))void assert (int v) { if (!v) __VERIFIER_error (); }


int main ()
{
  int SIZE = 10;
  int a[SIZE];

  int j=SIZE;
  int done=0;

  do
  {
    j--;
    if (a[j]==nd()) {
      //if (0>=j) __VERIFIER_error();
      assert (j > 0);
      //assert(j<SIZE);
      done = 1;
    }
  } while ( done==0 && j >= 0 );

  return done;
}
