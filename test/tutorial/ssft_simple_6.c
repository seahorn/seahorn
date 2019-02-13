// RUN: %shorntest %t-harness.ll %t-debug %s --max-depth=15 | OutputCheck %s --check-prefix=XFAIL_UNKNOWN
// RUN: %shorntest %t-harness0.ll %t-debug0 %s -O0 --max-depth=15 | OutputCheck %s
// RUN: %shorntest %t-harness1.ll %t-debug1 %s -O1 --max-depth=15 | OutputCheck %s --check-prefix=XFAIL_UNKNOWN
// RUN: %shorntest %t-harness2.ll %t-debug2 %s -O2 --max-depth=15 | OutputCheck %s --check-prefix=XFAIL_UNKNOWN
// RUN: %shorntest %t-harness3.ll %t-debug3 %s -O3 --max-depth=15 | OutputCheck %s --check-prefix=XFAIL_UNKNOWN
// CHECK: ^unsat$
// XFAIL_UNKNOWN: ^unknown$
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
