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

#include "seahorn/seasynth.h"

extern int nd1();
extern int nd2();
extern int nd3();

extern bool infer(int x);
bool PARTIAL_FN inv(int x)
{
    if (x == 0) return true;
    return infer(x);
}

// This program has two distinct paths.
// Along the first path, a synthesis assertion is made.
// Along the second path, a safety assertion is made.
// A solution to the first path is an invariant such that (x >= 0) => inv(x).
// The second path if safe if and only if inv(x) => (x < 5).
// Consequently, the program is unsafe.
int main(void)
{
    if (nd1())
    {
        int x = nd2();
        assume(inv(x));
	    x = x + 1;
	    sassert(inv(x));
    }
    else
    {
        int x = nd3();
	    assume(inv(x));
	    sassert(x < 5);
    }
}
