/**
 * An example of non-deterministic encoding. 
 * Usage:
 *    1. sea pf -O0 --show-invars <FILE>
 *    2. sea pf -O0 --show-invars -DFIXED_SIZE=40 <FILE>
 *
 * when FIXED_SIZE is specified, the solver unrolls the loop,
 * otherwise, it finds a generic inductive argument
 *   
 */
extern int nd (void);
extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern void __VERIFIER_assume(int);
__attribute__ ((__always_inline__)) void __VERIFIER_assert(int v) 
{if (!v) __VERIFIER_error ();}


#define assume __VERIFIER_assume
#define assert __VERIFIER_assert

int main(void)
{
  int base;
  int ptr;
  int size;
  int offset;

  int N;
  N = nd();
  assume (N > 0);

#ifdef FIXED_SIZE
  assume (N == FIXED_SIZE);
#endif
  
  base = nd();
  assume (base > 0);
  size = nd();
  assume (size > 0);
  ptr = 0;
  offset = 0;

  int addr = nd();
  assume (addr > 0);
  
  if (base == addr)
  {
    ptr = base;
    assume(size == 4*N);
  }
  else
    assume (base + size < addr);
  
  
  for (int i = 0; i < N; i++)
  {
    int p = addr + 4*i;
    if (nd())
    {
      if (ptr == addr)
      {
        ptr = p;
        offset += 4*i;
      }
    }
    
    
    int o;
#ifdef USE_BASE_OFF
    o = addr==base ? 4*i : offset;
#else
    o = offset;
#endif
    
    int sz;
#ifdef USE_BASE_SZ
    sz = addr==base ? 4*N : size;
#else
    sz = size;
#endif    
    
    if (addr == base || ptr == p)
    {
      assert (o >= 0);
      assert (o + 4 <= sz);
    }
  }
  
  return 0;
}
