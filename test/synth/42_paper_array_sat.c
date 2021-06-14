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

// Example: Find a compositional array invariant: ite(i == sid, SInv(max, v), GInv(max, v))
//
// int main(void)
// {
//     int size = *;
//     int *data = new int[size];
//     
//     memset(data, 0, sizeof(data));
//     int max = 0;
//     uint sid = *;
//     
//     while (true)
//     {
//         uint id = *;
//         if (id != sid)
//         {
//             data[id] += 1;
//             if (data[id] > max) { max = data[id]; }
//         }
//     }
// }
//
// Fault injected: claims that: forall i :: data[i] < 5

#include "seahorn/seasynth.h"

//
// Seahorn definitions.
//

extern int nd1(void);
extern int nd2(void);
extern int nd3(void);
extern int nd4(void);
extern int nd5(void);

extern bool infer(int, int);

bool PARTIAL_FN SInv(int max, int v)
{
    if (v == 0)
    {
        return true;
    }
    else
    {
        return infer(max, v);
    }
}

bool PARTIAL_FN GInv(int max, int v)
{
    if (v == 0)
    {
        return true;
    }
    else
    {
        return infer(max, v);
    }
}

//
// Encodes verification problem.
//

int main(void) {
    int max = 0;
    int sid = nd1();

    while (true)
    {
        // Selects elements.
        int id1 = nd2();
        int id2 = nd3();
        assume(id1 != id2);
        int v1 = nd4();
        int v2 = nd5();
        if (id1 == sid) { assume(SInv(max, v1)); } else { assume(GInv(max, v1)); }
        if (id2 == sid) { assume(SInv(max, v2)); } else { assume(GInv(max, v2)); }

        // Update.
        sassert(v1 <= 5);
        if (id1 != sid)
        {
            v1 = v1 + 1;
            if (v1 > max)
            {
                max = v1;
            }
        }

        // Closed.
        if (id1 == sid) { sassert(SInv(max, v1)); } else { sassert(GInv(max, v1)); }
        if (id2 == sid) { sassert(SInv(max, v2)); } else { sassert(GInv(max, v2)); }
    }

    return 0;
}
