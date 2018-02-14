// RUN: %sea bpf -O0 --horn-bmc-crab  --bmc=path --bound=10  --horn-stats --inline --horn-at-most-one-predecessor --log=bmc-progress "%s" 2>&1 | OutputCheck %s
// CHECK: ^sat$

extern int nd(void);
extern void __VERIFIER_error(void) __attribute__((noreturn));
#define assert(X) if(!(X)){__VERIFIER_error();}

int main(){
  int x,y;
  x=1; y=1;
  while(nd()) {
    if (nd()) {
      x++;
      y++;
    }
    if (nd()) {
      x++;
    }
  }
  
  assert (x==y);
  return 0;
}

