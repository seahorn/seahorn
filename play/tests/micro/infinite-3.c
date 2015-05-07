extern int  __VERIFIER_NONDET();
extern void __VERIFIER_assume(int);
extern void __VERIFIER_error(void);
void assert (int v) {if (!v) __VERIFIER_error ();}

int main(){
  int lock, old, new;
  
  old=0;
  lock=0;
  new=old+1;
  
  while (new != old) {
    lock = 1;
    old = new;
    if (__VERIFIER_NONDET()) {
      lock = 0;
      new++;
    }
  }
  assert (lock !=0);
  return 42;
}
