extern int nd ();
/*
from bixie
*/

extern void __VERIFIER_error (void);

void assert (int v) { if (!v) __VERIFIER_error (); }


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
      assert(0<=j && j<SIZE);
      done = 1;
    }
  } while ( done==0 && j >= 0 );

  return done;
}
