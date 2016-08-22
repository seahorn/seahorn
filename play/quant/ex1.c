/** 
   sea pf ex1.c --verbose=1 -O[0|1|2|3] 
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

  
  /* chose an element in array A*/
  r = nd ();

  /* initial state of the element pointed to by r */
  r_state = 0;
  
  /** create N distinct elements */
  for (int n = 0; n < N; n++)
  {
    A[n] = n;
  }
  
  // AG: Not sure we need to ensure that r picks something in A, it
  // can pick a value that is not in A as well.
  assume (0 <= r && r<= N-1);
  
  for (int n = 0; n < N; n++)
  {
    // r_state is increased if we are processing the chosen element
    if (r == A[n]) {r_state ++;}
  }
 
  for (int n = 0; n < N; n++)
  { 
    // r_state is decreased if we are processing the chosen element
    if (r==A[n]) {r_state --;}
  }
  
  // r_state is 0 because either it has never changed (we did not pick
  // anything in A), or it was incremented and decremented the same
  // number of times.
  sassert (r_state == 0);
  return 0;
}
