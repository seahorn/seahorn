#include <stdlib.h>

extern void __VERIFIER_assume (int);
extern int  __VERIFIER_NONDET(void);
extern void __VERIFIER_error (void) __attribute__((noreturn)); 
void sassert (int v) { if (!v) __VERIFIER_error (); }
#define assume __VERIFIER_assume 
#define nd __VERIFIER_NONDET

int x, y;
int nd();

int main ()
{
  int n = nd ();
  
  if (n) x = 4; else x = 10;
  if (n) y = 5; else y = 10;
  
  nd ();
  sassert (x != y);
}
