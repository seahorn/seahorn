#ifndef _SEAHORN__H_
#define _SEAHORN__H_
#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif
/**
   Marks an error location for the verifier

   Catastrophic failure that matters.
 */
extern void __VERIFIER_error(void);

/**
 A condition to be assumed to be true by the verifier

*/
extern void __VERIFIER_assume(bool);

/**
   Returns TRUE if \p offset number of bytes of \p ptr are allocated

    Requires support from the memory manager. Might be interpreted to always
    return TRUE or FALSE if the memory manager does not support it.
 */
extern bool sea_is_dereferenceable(void *ptr, intptr_t offset);
#ifdef __cplusplus
}
#endif

/* Convenience macros */
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))
#endif
