/*
 */
extern int __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
#define assume __VERIFIER_assume
#define assert(X) if(!(X)){__VERIFIER_error ();}
  
  
extern int arie;

extern int nd(void);

int main(void)
{
  int i;
  int e;
  int sz;
  
  sz = nd ();
  e = nd ();
  
  assume (sz > 0);
  assume (e == sz*4);

  
  int k = nd();
#ifdef MAXK
  assume (k = MAXK);
#endif  
  
  i = 0;
  do
  {
    /* need to say that i and e are divisible by 4.
       there are two ways to encode it:
    */
#ifdef USE_REM
    /* using theory of integers: remainder of division by 4 is 0 */
    assume (e % 4 == 0);

    /* 
     * llvm is smart enough to know that i%4==0 and optimizes the assumption away
     * we trick llvm by tangling a new value j and i using assumptions.
     */
    int j;
    j = nd ();
    arie = 1;
    assume (j == i);
    assume (j % 4 == 0);
#else    
    /* alternative encoding without relying on integer division.
     * We use the equivalence: i%4==0 iff (exists t :: i == 4*t) 
     */
    int t1, t2;
    t1=nd(); t2=nd();
    assume(i==4*t1);
    assume(e==4*t2);
#endif
    if (i < k) assert (i < e);
    i += 4;
  } while (i != e);
  

  /* assert (i <= e); */
  return 0;
}
