extern int __VERIFIER_NONDET();

int main(){
  int i, n;
  int a, b;
  i=0; 
  a=0;
  b=0;
  n = __VERIFIER_NONDET();
  if (n > 0){ 
    while (i < n){
      if (__VERIFIER_NONDET()){     	
        a=a+1;
        b=b+2;
      }
      else{
        a=a+2;
        b=b+1;
      }
      i++;
    }
    if (!(a+b == 3 *n))
      goto ERROR;
  }
SAFE: goto SAFE;
ERROR: return 0;
}
