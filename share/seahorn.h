#ifndef _SEAHORN__H_
#define _SEAHORN__H_
#ifdef __cplusplus
extern "C" {
#endif        
void __VERIFIER_error (void);
void __VERIFIER_assume (int);
#ifdef __cplusplus
}
#endif

#define assume __VERIFIER_assume
#define sassert(X) if(!(X)) __VERIFIER_error ()
#endif
