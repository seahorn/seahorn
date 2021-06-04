// RUN: %sea smt %s --step=small --inline -o %t.sm.inline.smt2
// RUN: %z3 %t.sm.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=large --inline -o %t.lg.inline.smt2
// RUN: %z3 %t.lg.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// CHECK: ^sat$

#include "seahorn/seahorn.h"

#define ALLOC_L1 0
#define ALLOC_L2 1

extern int nd1();
extern int nd2();
extern int nd3();
extern int nd4();
extern int nd5();
extern int nd6();
extern int nd7();
extern int nd8();
extern int nd9();

//
// The space invariant.
//

extern bool infer(int id_addr, int id_alloc, int data, int next_addr, int next_alloc);
bool PARTIAL_FN inv(int id_addr, int id_alloc, int data, int next_addr, int next_alloc)
{
    return infer(id_addr, id_alloc, data, next_addr, next_alloc);
}

//
// The single class, and its helper functions.
//

struct Node
{
    int id_addr;
    int id_alloc;
    int data;
    int next_addr;
    int next_alloc;
};

void push(struct Node *n)
{
    __VERIFIER_assert(inv(n->id_addr, n->id_alloc, n->data, n->next_addr, n->next_alloc));
}

void pull(struct Node *n)
{
    // All fields, except for the address and allocation site, are volatile.
    n->data = nd1();
    n->next_addr = nd2();
    n->next_alloc = nd3();
    assume(inv(n->id_addr, n->id_alloc, n->data, n->next_addr, n->next_alloc));
}

void newNode(struct Node *n, int data, int next_addr, int next_alloc)
{
    // Select a non-null address.
    n->id_addr = n->data = nd4();
    assume(n->id_addr != 0);

    // All other values are parameters.
    n->data = data;
    n->next_addr = next_addr;
    n->next_alloc = next_alloc;
}

//
// Program.
//

// See 15_jayhorn_unsat.c. This example has a fault injected such that the array
// access in the final loop can go out of bounds (from below).
int main(void)
{
    int argc = nd8();
    int size = 10;

    struct Node l1;
    l1.id_addr = 0;
    l1.id_alloc = ALLOC_L1;

    struct Node l2;
    l2.id_addr = 0;
    l2.id_alloc = ALLOC_L2;

    for (int i = 0; i < argc; ++i)
    {
        int d = nd9();
        if (d >= 0 && d < size)
        {
            newNode(&l1, d, l1.id_addr, l1.id_alloc);
            /* Annotation*/ push(&l1);
        }
        else
        {
            newNode(&l2, d, l2.id_addr, l2.id_alloc);
            /* Annotation*/ push(&l2);
        }
    }

    while (l1.id_addr != 0)
    {
        /* Annotation*/ pull(&l1);
        sassert(l1.data >= 1 && l1.data < size - 1);
    }
}
