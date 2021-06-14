// RUN: %sea smt %s --step=small -o %t.sm.smt2
// RUN: %z3 %t.sm.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=small --inline -o %t.sm.inline.smt2
// RUN: %z3 %t.sm.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=large -o %t.lg.smt2
// RUN: %z3 %t.lg.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=large --inline -o %t.lg.inline.smt2
// RUN: %z3 %t.lg.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// CHECK: ^sat$

// Example: Find an loop invariant of the form: Inv(i, y) && Inv(i, x)
//
// int mult_by_two(int x)
// {
//     y = 0;
//     for (i = 0; i < x; ++i)
//     {
//         y += 2;
//     }
//     assert(y == 2 * x);
// }
//
// Fault injected: add 3 on each iteration.

#include "seahorn/seasynth.h"

extern int nd1(void);
extern int nd2(void);
extern int nd3(void);
extern int nd4(void);

bool extern infer(int, int);
bool PARTIAL_FN Inv1(int x, int y) { return infer(x, y); }
bool PARTIAL_FN Inv2(int x, int y) { return infer(x, y); }

int main(void)
{
    int x = nd1();
    int y = 0;
    int i = 0;
    assume(x >= 0);
    sassert(Inv1(x, i));
    sassert(Inv2(i, y));

    x = nd2();
    y = nd3();
    i = nd4();
    assume(Inv1(x, i));
    assume(Inv2(i, y));
    if (i < x)
    {
        i += 1;
        y += 3;
        sassert(Inv1(x,i));
        sassert(Inv2(i,y));
        assume(false);
    }
    sassert(y == 2 * x);

    return 0;
}
