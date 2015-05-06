extern int  __VERIFIER_NONDET();
extern void __VERIFIER_assume(int);
extern void __VERIFIER_error(void);
void assert (int v) {if (!v) __VERIFIER_error ();}

int main()
{
  int i,j,x,y;
  i = __VERIFIER_NONDET();
  j = __VERIFIER_NONDET();
  
  if (i >0 && j >0)
  {
    x=i; y=j;
    while (x!=0){
      x--;
      y--;
    }
    if (i==j)
      assert (y == 0);
  }
  return 42;
}
