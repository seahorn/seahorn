/** 
   sea pf ex1.c  --verbose=1 -O[0|1|2|3] [-DAN=num|-DSN=num|-DUB=num|-DLB=num] 
   
-DAN=num  assumes that N=num
-DSN=num  sets N to num
-DUB=num  assumes that N is bounded by num from above
-DLB=num  assumes that N is bounded by num from below


Diverges with -O0 for most options.

For -O1 and above, loops are unrolled. Verification is proportional to
the size of the bound

*/
extern int nd(void);

extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
#define assume(v) __VERIFIER_assume (v);
#define assert(v) if(!(v)) __VERIFIER_error ();

static int r;
static int r_state;

int main(void)
{
  int N;
  int A[N];

  N=nd();

#ifdef AN
  assume(N==AN);
#endif
  
#ifdef SN
  N=SN;
#endif
  
#ifdef UB
  assume(N>=1);
  assume(N<=UB);
#endif

#ifdef LB
  assume (N>=LB)
#endif
  
  /* chose an element */
  r = nd ();
  /* initial state of element pointed to by r */
  r_state = 0;
  
  /** create N distinct elements */
  for (int n = 0; n < N; n++) A[n] = n;
  
  /** at this point, there is no way to communicate to the next loop
      that all elements of A are distinct */
  
  /** count number of tracked elements */
  for (int n = 0; n < N; n++)
  {
    int s = A[n];
    /** state is increased multiple time if (exists i, j :: i<j & A[i]=A[j]) */
    if (s == r) r_state++;
  }
  
  /** assert that there is at most one tracked */
  assert (r_state <= 1);
  return 0;
}
