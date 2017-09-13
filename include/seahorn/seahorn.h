#ifndef _SEAHORN__H_
#define _SEAHORN__H_
#ifdef __cplusplus
extern "C" {
#endif        
extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
#ifdef __cplusplus
}
#endif

#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error (), 0))
#endif
