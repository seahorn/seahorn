extern int nd ();

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
__attribute__((always_inline)) void assert (int v) { if (!v) __VERIFIER_error (); }

int main ()
{

  int x = nd();
  int y=x;
  int flag = 0;

  do 
  {
	if (y==x) {
		flag = 1;
	}
	y++;
	x--;
  } while ( x > 0 );

  assert(flag == 0);
  return x;
}
