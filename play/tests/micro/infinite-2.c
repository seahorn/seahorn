extern int __VERIFIER_NONDET();

int main(){
  int i,j,x,y;
  i = __VERIFIER_NONDET();
  j = __VERIFIER_NONDET();
  if (i > 0 && j > 0){
    x=i; y=j;
    while (x!=0){
      x--;
      y--;
    }
    if (i==j && y>0)
      goto ERROR;
  }

SAFE: goto SAFE;
ERROR: return 0;
}
