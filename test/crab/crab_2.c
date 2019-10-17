// RUN: %sea pf -O0  --max-depth=20 "%s" 2>&1 | OutputCheck %s
// RUN: %sea pf -O0  --crab --max-depth=20 --horn-use-invs=inactive "%s" 2>&1 | OutputCheck %s
// RUN: %sea pf -O0  --crab --max-depth=20 --horn-use-invs=always "%s" 2>&1 | OutputCheck %s
// CHECK: ^unknown$
// XFAIL: *

// with --crab enabled and running with zones as default abstract
// domain the property can be trivially proven. To see divergence,
// need to compile with option -DALL_CRAB_DOMAINS and use a weaker
// domain such as intervals.

extern int nd(void);
extern void print(int);
extern void __VERIFIER_error(void) __attribute__((noreturn));
extern void __VERIFIER_assume (int);
#define assume __VERIFIER_assume
#define sassert(X) if(!(X)){__VERIFIER_error();}

#define N 10000

int main(){

  int k = nd();
  assume(k == N);  
  /* This loop is needed to make sure that the assumption is not in
     the same horn clause that initialization of x and y */
  while(nd()){}
    
  int x,y,z;
  x=1; y=0; z=0;
  /* we need AI to infer y >= 0*/
  while (nd ()) {
    x=x+y;
    y++;
  }

  /* 
     This loop is irrelevant to the assertion.
     Even with crab, this loop causes divergence in spacer.
   */
  while (z < k) { z = z + 2; }
  print(z); // to avoid -O3 to remove the loop

  sassert (x>=y);
  return 0;
}
