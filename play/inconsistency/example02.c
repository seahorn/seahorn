extern int nd();

__attribute__((always_inline)) void assert (int v) { if (!v) __VERIFIER_error (); }

int main ()
{
  int a = nd ();
  int y=0;
  if (a != 0)
  {
    y=1;
  }
  if (y==0)
  {
    assert (a != 0);
  }
  y++;
  
  return 42;
  
}
