extern int __VERIFIER_NONDET();

#define TRUE 1

int main(){
  int n=0;
  while (TRUE){
    if (__VERIFIER_NONDET())
      continue;
    if (n < 60) n++; else n=0;
    if (!( n >=0 && n <= 60))
      goto ERR;
  }

SAFE: goto SAFE;
ERR: return 42;
}
