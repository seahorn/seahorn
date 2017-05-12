#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

  typedef ptrdiff_t sea_ptrdiff_t;
  /* need size to be signed */
  typedef ptrdiff_t sea_size_t;

  extern  int8_t *  nd_int8_ptr (void);
  extern int64_t nd_int64_t (void);
  extern sea_size_t nd_sea_size_t (void);

  static int8_t* sea_bad_ptr;
  static bool sea_active;
  static int8_t *sea_top_alloc;

  extern void __VERIFIER_assume (int);
  __attribute__((__noreturn__)) extern void __VERIFIER_error (void);

#define assume __VERIFIER_assume
#define assert(X) if(!(X)){__VERIFIER_error ();}

  /* __attribute__((always_inline)) void assert  (int v)  { if (!v) __VERIFIER_error (); } */

  __attribute__((used)) void sea_abc_assert_valid_ptr (int8_t *base, sea_ptrdiff_t offset);
  __attribute__((used)) void sea_abc_assert_valid_offset (sea_ptrdiff_t offset, sea_size_t size);
  __attribute__((used)) void sea_abc_log_ptr (int8_t *base, sea_ptrdiff_t offset);
  __attribute__((used)) void sea_abc_log_load_ptr (int8_t *lhs, int8_t *ptr);
  __attribute__((used)) void sea_abc_log_store_ptr (int8_t *value, int8_t *ptr);    
  __attribute__((used)) void sea_abc_alloc (int8_t *base, sea_size_t size);
  __attribute__((used)) void sea_abc_init(void);
  
#ifdef __cplusplus
}
#endif
 
/*
 * checks that base + offset is a valid pointer
 * insert after every load/store when size is unknown
 * base is a base pointer of some gep
 * offset is the computed offset _Should be adjusted for used size if needed_
 */

void sea_abc_assert_valid_ptr (int8_t *base, sea_ptrdiff_t offset)
{
  /* base is not tracked, or base + offset is below bad region */
  assert (base > sea_bad_ptr || base + offset < sea_bad_ptr);
}

/**
 * insert after every load/store when offset and size are known
 * offset is the computed offset
 * size is a constant size
 */
void sea_abc_assert_valid_offset (sea_ptrdiff_t offset, sea_size_t size)
{
   assert (offset <= size);
  /* TODO: do not know how to check for underflow */
}

/**
 * insert after every p = gep(base, offset), if p is used indirectly
 * base - the base argument to gep
 * offset - the computed offset from gep + used_size
 */
void sea_abc_log_ptr (int8_t *base, sea_ptrdiff_t offset) {}

/**
 * insert extra assumptions when a pointer is read from memory.
 * lhs := mem[ptr], where lhs is a pointer
 * ptr - pointer operand of the load
 * lhs - lhs of the load
 **/
void sea_abc_log_load_ptr (int8_t *lhs, int8_t *ptr /*unused*/) {}

/**
 * insert extra assertions when a pointer is written into memory.
 * mem[ptr] := value, where value is a pointer
 * ptr - pointer operand of the store 
 * value - pointer value of the store
 **/
void sea_abc_log_store_ptr (int8_t *value, int8_t *ptr /*unused*/) {}

/**
 * insert after every allocation instruction
 * base - pointer to allocated buffer
 * size - the size of the allocated buffer
 */
void sea_abc_alloc (int8_t *base, sea_size_t size)
{
  /* assume all pointers are strictly positive
     (and trick LLVM into not reducing the assumption to nothing)
  */
  int8_t *tmp = nd_int8_ptr ();
  assume (((ptrdiff_t)tmp) > 0);
  assume (tmp == base);
  
  if (nd_sea_size_t ())
  {
    /* at some point, allocate a pointer below the bad region */
    assume (!sea_active);
    sea_active = true;
    assume (base + size < sea_bad_ptr);
  }
  else
  {
    /* in the normal mode, allocate above the bad region */
    assume (base > sea_top_alloc);
    assume (/* optional */ sea_top_alloc > sea_bad_ptr); 
    sea_top_alloc += size;
  }
}

void sea_abc_init(void)
{
  /* pick a bad pointer. A bad pointer is an address that should never
     be accessed */
  sea_bad_ptr = nd_int8_ptr ();
  int8_t *tmp = nd_int8_ptr ();
  assume (((ptrdiff_t)tmp) > 0);
  assume (tmp == sea_bad_ptr);
  
  sea_active = false;
  sea_top_alloc = nd_int8_ptr ();
  assume (sea_top_alloc > sea_bad_ptr);
}

