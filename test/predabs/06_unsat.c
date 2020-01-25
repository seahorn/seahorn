// RUN: %sea --mem=-1 -m64 pf --step=large -g --horn-global-constraints=true --track=mem --horn-stats --enable-nondet-init --strip-extern --externalize-addr-taken-functions --horn-singleton-aliases=true --devirt-functions=types --horn-ignore-calloc=false --enable-indvar --enable-loop-idiom --horn-make-undef-warning-error=false --inline "%s" --horn-pred-abs
// CHECK: ^unsat$

#include "seahorn/seahorn.h"
int unknown1();


int main()
{
    int x=1; int y=1;
    while(unknown1()) {
        int t1 = x;
        int t2 = y;
        x = t1+ t2;
        y = t1 + t2;
    }
    sassert(y >=1);
    return 0;
}
