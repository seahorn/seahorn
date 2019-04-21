// RUN: %sea bpf -O0 --bmc=mono --bound=10  --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O0 --horn-bmc-crab=false  --bmc=path --horn-bmc-muc=assume --bound=10  --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O0 --horn-bmc-crab=false  --bmc=path --horn-bmc-muc=quickXplain --bound=10  --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O0 --horn-bmc-crab=true  --bmc=path --bound=10  --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O0 --horn-gsa --bmc=mono --bound=10  --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// CHECK: ^unsat$

/** 
 * All the if-then-else's are irrelevant to the assertion. The BMC
 * engine is smart enough to realize and it explores only one path.
**/

extern int nd(void);
extern void __VERIFIER_error(void) __attribute__((noreturn));
extern void __VERIFIER_assume (int);
#define assert(X) if(!(X)){__VERIFIER_error();}
#define assume __VERIFIER_assume

int main(){
  int x,y,z;
  int p1,p2,p3;

  int a = nd();
  assume(a>0);
  
  x=nd();
  y=nd();
  z=nd();

  if (nd()) {
    p1 = 1;
  } else {
    p1 = 0;
  }
  
  while(nd()){}
  
  if (nd()) {
    p2 = 1;
  } else {
    p2 = 0;
  }

  while(nd()){}
  
  if (nd()) {
    p3 = 1;
  } else {
    p3 = 0;
  }

  while(nd()){}  

  if (p1) {
    x++;
  } else {
    x--;
  }

  while(nd()){}
  
  if (p2) {
    y++;
  } else {
    y--;
  }

  while(nd()){}
  
  if (p3) {
    z++;
  } else {
    z--;
  }
  
  
  
  assert (a>=0);
  return 0;
}
