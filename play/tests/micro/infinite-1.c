extern int __VERIFIER_NONDET();

int main(){
  int x,y;
  x=1; y=0;
  while (__VERIFIER_NONDET()){
    x=x+y;
    y++;
  }

  if (!(x>=y))
    goto ERROR;

SAFE: goto SAFE;
ERROR: return 0;
}
