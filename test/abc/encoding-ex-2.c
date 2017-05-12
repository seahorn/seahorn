extern int nd (void);
extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern void __VERIFIER_assume(int);
__attribute__ ((__always_inline__)) void __VERIFIER_assert(int v) 
{if (!v) __VERIFIER_error ();}


#define assume __VERIFIER_assume
#define assert __VERIFIER_assert

int base;
int ptr;
int size;
int offset;

int foo (int addr, int n, int v)
{
  for (int i = 0; i < n; ++i)
  {
    /* deref addr + 4*i */;
    int o = base == addr ? 4*i : offset + 4*i;
    if (base == addr || ptr == addr)
      assert (o + 4 <= size);
  }
  return addr;
}

int main(void)
{
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
  
  /* addr = alloc(4*N) */
  if (base == addr)
  {
    ptr = base;
    assume(size == 4*N);
  }
  else
    assume (base + size < addr);
  
  int x;
  x = nd();
  assume (x == 5);
  
  int b = foo (addr, N, x);
  int c = foo (b, N, x+1); 
  
  return 0;
}
