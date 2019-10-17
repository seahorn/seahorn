// RUN: %sea bpf -O0 --bmc=mono --bound=10  --horn-stats --inline  "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O0 --horn-bmc-crab=false  --bmc=path --horn-bmc-muc=assume --bound=10  --horn-stats --inline  "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O0 --horn-bmc-crab=false  --bmc=path --horn-bmc-muc=quickXplain --bound=10  --horn-stats --inline  "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O0 --horn-bmc-crab=true  --bmc=path --bound=10  --horn-stats --inline  "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O0 --horn-gsa --bmc=mono --bound=10  --horn-stats --inline  "%s" 2>&1 | OutputCheck %s
// CHECK: ^unsat$

/* Basic functionality */

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
  
  assert (x>=y);
  return 0;
}

