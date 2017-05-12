/*
 * sea pf /tmp/test.c  -O0 --verbose=1 --show-invars [-DDIVERGE]
 */
extern int __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
#define assume __VERIFIER_assume
#define assert(X) if(!(X)){__VERIFIER_error ();}
  

extern void use(int);


extern int nd(void);

int main(void)
{
  int j;
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
  
  /** 
   * rewrite the loop so that the induction variable is incremented by 1
   * 
   */
  j = 0;
  do
  {
    i = nd();
    /* prevent llvm from optimizing */
    assume(i == 4*j);
    
#ifndef DIVERGE
    assert (e >= 4*sz);
    assert (e <= 4*sz);
    
    /* an alternative assertion that leads to  longer proof */
    /* assert (e > sz); */
#endif
    
    if (i < k) assert (i < e);
    j = j+1;
    i = nd();
    assume (i == 4*j);
  } while (i != e);
  

  /* assert (i <= e); */
  return 0;
}
