// RUN: %sea bpf -O0 --bound=10 --bmc=path --horn-bmc-crab=true --horn-bmc-crab-invariants=true --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// CHECK: Boolean abstraction is already false
// CHECK: ^unsat$

/* Test option --horn-bmc-crab-invariants */
extern int nd(void);
extern void __VERIFIER_error(void) __attribute__((noreturn));
extern void __VERIFIER_assume (int);
extern void avoid_select_inst(void);
#define assert(X) if(!(X)){__VERIFIER_error();}
#define assume __VERIFIER_assume

int main(){
  int p = 0;
  
  if (nd()) {
    p++;
    avoid_select_inst();
  } else {
    p+=2;
  }

  if (nd()) {
    p++;
    avoid_select_inst();    
  } else {
    p+=2;
  }
  
  if (nd()) {
    p++;
    avoid_select_inst();    
  } else {
    p+=2;
  }

  if (nd()) {
    p++;
    avoid_select_inst();    
  } else {
    p+=2;
  }

  if (nd()) {
    p++;
    avoid_select_inst();            
  } else {
    p+=2;
  }

  if (nd()) {
    p++;
    avoid_select_inst();            
  } else {
    p+=2;
  }

  assert(p <= 12);
  return 0;
}
