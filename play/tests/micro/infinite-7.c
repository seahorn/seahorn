extern int __VERIFIER_NONDET();

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
    if (y > x)
      goto ERROR;
  }
SAFE: goto SAFE;
ERROR: return 0;
}
