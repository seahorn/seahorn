extern int  __VERIFIER_NONDET();
extern void __VERIFIER_assume(int);
extern void __VERIFIER_error(void);
void assert (int v) {if (!v) __VERIFIER_error ();}

int main(){
  int x=0;
  int y=0;
  int n;
  if (n>=0){
    while (x < n) {
      x = x + 1;
      y = y + 1;
    }
    while (x > 0) {
      x = x - 1;
      y = y - 1;
    }
    assert (y <= x);
  }
  return 42;
}
