// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// CHECK: ^unsat$

/* requires -O0 */

int unknown(void);
int unknown1(void);

extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
void assert (int v) { if (!v) __VERIFIER_error (); }


#define assume __VERIFIER_assume
#define static_assert assert

int main(void)
{
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

  while(unknown())
  {
    while(unknown1())
    {
       if(x==y)
          i++;
       else
          j++;
    }
    if(i>=j)
    {
       x++;
       y++;
    }
    else
       y++;
  }

  static_assert(i>=j);
}
