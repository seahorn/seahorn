#ifndef _SEAHORN__H_
#define _SEAHORN__H_
extern "C" void __VERIFIER_error (void);
extern "C" void __VERIFIER_assume (int);

#define assume __VERIFIER_assume
#define sassert(X) if(!X) __VERIFIER_error ()
  
#endif
