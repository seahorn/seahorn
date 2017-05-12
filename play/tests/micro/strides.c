/*
 * sea pf /tmp/test.c  -O0 --verbose=1 -DSTEP=2 -DMAXK=16 --show-invars 
 * diverges for
 * sea pf /tmp/test.c  -O0 --verbose=1 -DSTEP=4 --show-invars 
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

#ifndef STEP
#define STEP 1
#endif
  
  int k = nd();
#ifdef MAXK
  assume (k = MAXK);
#endif  
  
  i = 0;
  assert (i + 4 <= e)
  do
  {
    if (i < k) assert (i+STEP <= e);
    i += STEP;
  } while (i != e);
  

  /* assert (i <= e); */
  return 0;
}
