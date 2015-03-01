extern int __VERIFIER_NONDET();
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
  if (x>=0) 
    goto SAFE;
  else 
    goto ERROR;
  
SAFE: goto SAFE;
ERROR: return 0;
}

