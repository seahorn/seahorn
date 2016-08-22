/** 
   
    Manually generated hints by Limin Jia <liminjia@cmu.edu>
    
   sea pf ex1_instrumented.c --verbose=1 -O[0|1|2|3] 

Diverges with -O0 for most options.

For -O1 and above, loops are unrolled. Verification is proportional to
the size of the bound

*/
#include <seahorn/seahorn.h>
extern int nd(void);


static int r;
static int r_state;

int main(void)
{
  int N;
  N = nd();
  
  int A[N];

  
  /* chose an element */
  r = nd ();

  /* initial state of element pointed to by r */
  r_state = 0;
  
  /** create N distinct elements */
  for (int n = 0; n < N; n++)
  {
    A[n] = n;
    sassert (n <= 0 || A[n-1] == A[n] - 1);
  }
  
  //sassert (r_state == 0);
  assume (0 <= r && r<= N-1);
  for (int n = 0; n < N; n++)
  {
    // LIMIN: Why can't I sassert the following?
    //sassert (n <= 0 || A[n-1] == A[n]-1);
    assume (n <= 0 || A[n-1] == A[n]-1);
    sassert((r_state == 0 && r >= A[n]) || (r_state == 1 && r < A[n]));
    //assume((r_state == 0 && r >= A[n]) || (r_state == 1 && r < A[n]));
    if (r == A[n]) {r_state ++;}
    sassert ((r_state == 0 && r > A[n]) || (r_state == 1 && r <= A[n]));
  }
  sassert ((r_state == 0 && r > A[N-1]) || (r_state == 1 && r <= A[N-1]));
  sassert (r_state ==1);
 
  for (int n = 0; n < N; n++)
  { assume (n <= 0 || A[n-1] == A[n]-1);
    sassert (r >= A[0]);
    sassert ((r_state == 0 && r < A[n]) || (r_state == 1 && r >= A[n]));
    // assume ((r_state == 0 && r < A[n]) || (r_state == 1 && r >= A[n]));
    if (r==A[n]) {r_state --;}
    sassert ((r_state == 0 && r <= A[n]) || (r_state == 1 && r > A[n]));
  }
  // LIMIN: Why can't I sassert the following? It works for the previous loop. What's wrong here?
  //sassert ((r_state == 0 && r <= A[N-1]) || (r_state == 1 && r > A[N-1]));
  assume ((r_state == 0 && r <= A[N-1]) || (r_state == 1 && r > A[N-1]));
  sassert (r_state == 0);
  return 0;
}
