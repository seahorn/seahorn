extern int  __VERIFIER_NONDET();
extern void __VERIFIER_assume(int);
extern void __VERIFIER_error(void);
void assert (int v) {if (!v) __VERIFIER_error ();}

int main(){
  int x,y;
  x=1; y=0;
  while (__VERIFIER_NONDET()){
    x=x+y;
    y++;
  }

  assert ((x>=y));
  return 42;
}
