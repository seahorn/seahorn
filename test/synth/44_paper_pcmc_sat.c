// RUN: %sea smt %s --step=small --inline -o %t.sm.inline.smt2
// RUN: %z3 %t.sm.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=large --inline -o %t.lg.inline.smt2
// RUN: %z3 %t.lg.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// CHECK: ^sat$

// Example: Find a compositional invariant for a ring running: v' = tr(v)
//
// enum Lock { Free, Left, Right }
// enum State { Trying, Critical }
// struct View { Lock left; State st; Lock right; }
// 
// State tr(View v)
// {
//     if (view.s == Critical)
//     {
//         view.s = Trying;
//         view.left = Free;
//         view.right = Free;
//     }
//     else
//     {
//         if (v.left == Left && v.Right == Right) { v.st = Critical; }
//         else if (view.left == Free) { view.left = LEFT; }
//         else if (view.right == Free) { view.right = RIGHT; }
//     }
//     return view;
// }
//
// Injected fault: Can acquire critical section without both forks.

#include "seahorn/seasynth.h"

//
// Process Definition.
//

enum Lock { Free, Left, Right };
enum State { Trying, Critical };
struct View { enum Lock left; enum State st; enum Lock right; };

void tr(struct View *v)
{
    if (v->st == Critical)
    {
        v->st = Trying;
        v->left = Free;
        v->right = Free;
    }
    else
    {
        if (v->left == Left || v->right == Right)
        {
            v->st = Critical;
        }
        else if (v->left == Free)
        {
            v->left = Left;
        }
        else if (v->right == Free)
        {
            v->right = Right;
        }
    }
}

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

bool infer(enum Lock, enum State, enum Lock);
bool PARTIAL_FN Inv(enum Lock left, enum State st, enum Lock right)
{
    if (left == Free && st == Trying && right == Free)
    {
        return true;
    }
    else
    {
        return infer(left, st, right);
    }
}

//
// Encodes verification problem.
//

int main(void)
{
    if (nd1())
    {
        struct View v1;
        v1.left = nd2();
        v1.st = nd3();
        v1.right = nd4();
        assume(Inv(v1.left, v1.st, v1.right));

        enum State st2 = nd5();
        assume(Inv(v1.right, st2, v1.left));

        tr(&v1);
        sassert(Inv(v1.left, v1.st, v1.right));
        sassert(Inv(v1.right, st2, v1.left));
    }
    else
    {
        struct View v;
        v.left = nd6();
        v.st = nd7();
        v.right = nd8();
        assume(Inv(v.left, v.st, v.right));

        sassert(v.st != Critical || (v.left == Left && v.right == Right));
    }

    return 0;
}
