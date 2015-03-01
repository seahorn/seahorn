extern int __VERIFIER_NONDET();

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
  if (lock != 0)
    goto SAFE;
  else 
    goto ERROR;

SAFE: goto SAFE;
ERROR: return 0;

}
