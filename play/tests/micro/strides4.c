/*
 * sea pf  ./strides4.c  -O0 --verbose=1   --show-invars   -DSTEP=4
 */
extern int __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
#define assume __VERIFIER_assume
#define assert(X) if(!(X)){__VERIFIER_error ();}
  
  

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
  
#ifndef STEP
#define STEP 1
#endif
  
  i = 0;
  do
  {
    if (i < k) assert (i<e);
    i += STEP;
  } while (i+STEP<=e /* instead of i<e */);
  

  assert (i <= e);
  return 0;
}
