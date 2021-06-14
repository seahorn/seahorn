// RUN: %sea smt %s --step=small --inline -o %t.sm.inline.smt2
// RUN: %z3 %t.sm.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=large --inline -o %t.lg.inline.smt2
// RUN: %z3 %t.lg.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// CHECK: ^sat$

// Example: Find a class invariant such that the program is safe.
//
// class Counter
// {
//     int max; int pos;
//     Counter(int _max)
//     {
//         assume(max > 0);
//         max = _max; pos = 0;
//     }
//     void reset() { pos = 0; }
//     int capacity() { return max - pos; }
//     bool increment()
//     {
//         if (pos >= max) { return false; }
//         pos += 1;
//         return true;
//     }
// }
//
// void drain(Counter o)
// {
//     while (o.capacity() != 0) { assert(o.increment()); }
//     o.reset();
//     assert(o.capacity() > 0);
// }
//
// Injected fault: `o.capacity() >= 0` such that increment() will fail.

#include "seahorn/seasynth.h"

//
// Seahorn definitions.
//

extern int nd1(void);
extern int nd2(void);
extern int nd3(void);
extern int nd4(void);
extern int nd5(void);
extern int nd6(void);
extern int nd7(void);
extern int nd8(void);
extern int nd9(void);
extern int nd10(void);

bool extern infer(int, int);
bool PARTIAL_FN Inv(int max, int pos) { return infer(max, pos); }

//
// Encodes class as a c-struct with helper methods.
//

struct Counter { int max; int pos; };

void Counter_ctor(struct Counter *o, int _max)
{
    assume(_max > 0);
    o->max = _max;
    o->pos = 0;
}

void Counter_reset(struct Counter *o) { o->pos = 0; }

int Counter_capacity(struct Counter *o) { return (o->max - o->pos); }

bool Counter_increment(struct Counter *o)
{
    if (o->pos >= o->max) { return false; }
    o->pos += 1;
    return true;
}

//
// Encodes verification problem.
//

int main(void)
{
    int rule = nd1();
    if (rule == 0)
    {
        // Base case.
        struct Counter o;
        Counter_ctor(&o, nd2());
        sassert(Inv(o.max, o.pos));
    }
    else if (rule == 1)
    {
        // Invariant is closed under reset().
        struct Counter o; o.max = nd3(); o.pos = nd4();
        assume(Inv(o.max, o.pos));
        Counter_reset(&o);
        sassert(Inv(o.max, o.pos));
    }
    else if (rule == 2)
    {
        // Invariant is closed under capacity().
        struct Counter o; o.max = nd5(); o.pos = nd6();
        assume(Inv(o.max, o.pos));
        Counter_capacity(&o);
        sassert(Inv(o.max, o.pos));
    }
    else if (rule == 3)
    {
        // Invariant is closed under increment().
        struct Counter o; o.max = nd7(); o.pos = nd8();
        assume(Inv(o.max, o.pos));
        Counter_increment(&o);
        sassert(Inv(o.max, o.pos));
    }
    else
    {
        // Assume that drain(o) is called on an arbitrary o.
        struct Counter o; o.max = nd9(); o.pos = nd10();
        assume(Inv(o.max, o.pos));

        // Assert that drain(o) is safe.
        while (Counter_capacity(&o) >= 0)
        {
            bool res = Counter_increment(&o);
            sassert(res);
        }
        Counter_reset(&o);
        sassert(Counter_capacity(&o) > 0);
    }

    return 0;
}
