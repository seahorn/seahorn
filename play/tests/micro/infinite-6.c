extern int  __VERIFIER_NONDET();
extern void __VERIFIER_assume(int);
extern void __VERIFIER_error(void);
void assert (int v) {if (!v) __VERIFIER_error ();}

int main(){
  int x=0;
  int y=0;
  while (__VERIFIER_NONDET()) {
    if (__VERIFIER_NONDET()) {
      x = x+1; 
      y = y+2;
    } 
    else{
      x = x+2; 
      y = y+1; 
    }
  }
  assert (x>=0);
  return 42;
}

