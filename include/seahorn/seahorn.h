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

extern void __VERIFIER_assert(bool);
extern void __VERIFIER_assert_not(bool);
extern void __VERIFIER_assert_if(bool, bool);
/**
   Returns TRUE if \p offset number of bytes of \p ptr are allocated

    Requires support from the memory manager. Might be interpreted to always
    return TRUE or FALSE if the memory manager does not support it.
 */
extern bool sea_is_dereferenceable(void *ptr, intptr_t offset);
extern void sea_assert_if(bool, bool);
/* returns true if memory pointed to by arg has been modified from
 * 1. allocation OR
 * 2. reset_modified OR
 * 3. sea_tracking_on
 * whichever is the latest event.
 */
extern bool sea_is_modified(char *);
/* tracking is set to on for subsequent program till exit or sea_tracking_off */
extern void sea_tracking_on(void);
/* tracking is set to off for subsequent program till exit or sea_tracking_on */
extern void sea_tracking_off(void);
/* reset modified metadata for memory pointed to by arg */
extern void sea_reset_modified(char *);
#ifdef __cplusplus
}
#endif

/* Convenience macros */
#define assume __VERIFIER_assume

#define PARTIAL_FN                                                             \
  __attribute__((annotate("partial"))) __attribute__((noinline))

/* See https://github.com/seahorn/seahorn/projects/5 for details */
#ifdef VACCHECK
#define sassert(X)                                                             \
  (void)((__VERIFIER_assert(X), (X)) || (__VERIFIER_error(), 0))
#else
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))
#endif

#endif
