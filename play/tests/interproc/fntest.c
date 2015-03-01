extern void __VERIFIER_error() __attribute__((noreturn));
/* extern void __VERIFIER_error(); */
extern int nd();


int foo (int x)
{
  if (x > 10) __VERIFIER_error ();
  x++;
  return x;
}

int main(void)
{
  int x, y;
  x = nd();
  
  y = foo (x);
  x = y;
  y = foo (x);
  
  return 0;
}

