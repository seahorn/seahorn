extern int __VERIFIER_NONDET();

#define TRUE 1

int main(){
  int s = 0;
  while(TRUE){
    if (__VERIFIER_NONDET())
      break;
    if (s < 5)
      s++;
    else
      s=0;
  }
  if (s >= 0 && s <= 5)
    goto SAFE;

ERROR: return 42;
SAFE: goto SAFE;
}
