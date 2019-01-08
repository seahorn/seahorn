// RUN: %sea bpf -O0 --bmc=mono --bound=10  --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O0 --horn-bmc-crab=false  --bmc=path --bound=10  --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O0 --horn-bmc-crab=true  --bmc=path --bound=10  --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O0 --horn-gsa --bmc=mono --bound=10  --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// CHECK: ^sat$

/** 
 * The number of paths grows exponentially on the number of
 * if-then-else's.
 * 
 * The paths are not discharged by crab unless it uses a domain like
 * zones.
 **/

extern int nd(void);
extern void __VERIFIER_error(void) __attribute__((noreturn));
#define assert(X) if(!(X)){__VERIFIER_error();}

#define ENSURE_DIFFERENT_BLOCK while(nd()){}

int main(){
  int x,y;
  x=1; y=1;
  
  if (nd()) {
    x++;
    y++;
  }

  ENSURE_DIFFERENT_BLOCK;;
  
  if (nd()) {
    x++;
    y++;
  }

  ENSURE_DIFFERENT_BLOCK;;  
 
  if (nd()) {
    x++;
    y++;
  }

  ENSURE_DIFFERENT_BLOCK;;    
  
  if (nd()) {
    x++;
    y++;
  }

  ENSURE_DIFFERENT_BLOCK;;      
 
  if (nd()) {
    x++;
    y++;
  }

  ENSURE_DIFFERENT_BLOCK;;
  
  if (nd()) {
    x++;
    y++;
  }

  ENSURE_DIFFERENT_BLOCK;;
  
  if (nd()) {
    x++;
    y++;
  }

  /* ENSURE_DIFFERENT_BLOCK;; */
  
  /* if (nd()) { */
  /*   x++; */
  /*   y++; */
  /* } */

  /* ENSURE_DIFFERENT_BLOCK;;   */
 
  /* if (nd()) { */
  /*   x++; */
  /*   y++; */
  /* } */

  /* ENSURE_DIFFERENT_BLOCK;;     */
  
  /* if (nd()) { */
  /*   x++; */
  /*   y++; */
  /* } */
  
  assert (x>y);
  return 0;
}
