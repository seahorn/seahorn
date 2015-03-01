extern int __VERIFIER_NONDET();

int main(){
  int e, s;
  e=0;
  s=2;  
  while (__VERIFIER_NONDET()) {
    if (s == 2){
      if (e ==0) e=1;
      s = 3;
    }
    else if (s == 3){
      if (e ==1) e=2;
      s=4;
    }
    else if (s == 4){
      if (e == 3)
        goto ERROR;
      s=5;
     }
  }
SAFE: goto SAFE;
ERROR: return 0;
}

