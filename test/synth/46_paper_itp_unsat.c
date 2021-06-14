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
// CHECK: ^unsat$

#include "seahorn/seasynth.h"

extern int nd1(void);
extern int nd2(void);
extern int nd3(void);
extern int nd4(void);

bool extern infer(int, int);
bool PARTIAL_FN Inv(int x, int y) { return infer(x, y); }

int main(void)
{
    int x = 0;
    int y = nd1();
    assume(y > 0);

    int i = 0;
    while (i < y)
    {
        x += 1;
        i += 1;
    }
    sassert(Inv(x, y));
    
    x = nd2();
    y = nd3();
    assume(Inv(x, y));
    sassert(x == y);

    return 0;
}
