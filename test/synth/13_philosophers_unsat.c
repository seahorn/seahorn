// RUN: %sea smt %s --step=small --inline -o %t.sm.inline.smt2
// RUN: %z3 %t.sm.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=large --inline -o %t.lg.inline.smt2
// RUN: %z3 %t.lg.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// CHECK: ^unsat$

#include "seahorn/seasynth.h"

extern int nd1();
extern int nd2();
extern int nd3();
extern int nd4();
extern int nd5();
extern int nd6();
extern int nd7();
extern int nd8();

// The shared state of a fork variable.
#define FORK_AVAILABLE 0
#define FORK_LEFT 1
#define FORK_RIGHT 2

// The internal state of a philosopher process.
#define PHIL_THINKING 0
#define PHIL_HUNGRY 1
#define PHIL_EATING 2

// Compositional invariant for a dining philosopher.
extern bool infer(int left_fork, int phil, int right_fork);
bool PARTIAL_FN inv(int left_fork, int phil, int right_fork)
{
    // Initial state (base case).
    if (phil == PHIL_THINKING && left_fork == FORK_AVAILABLE && right_fork == FORK_AVAILABLE)
    {
        return true;
    }

    // Synthesized function.
    return infer(left_fork, phil, right_fork);
}

// The transition function for a philosopher.
void tr(int *left_fork, int *phil, int *right_fork)
{
    // If the process is thinking, it can transition to hungry.
    if (*phil == PHIL_THINKING)
    {
        *phil = PHIL_HUNGRY;
        return;
    }
    // If the philosopher is hungry, then it will try to acquire the fork.
    else if (*phil == PHIL_HUNGRY)
    {
        // If both forks are aquired, the philosopher will eat.
        if (*left_fork == FORK_RIGHT && *right_fork == FORK_LEFT)
        {
            *phil = PHIL_EATING;
            return;
        }
        // If neither fork is in use, then the philosopher remains hungry.
        else if (*left_fork == FORK_LEFT && *right_fork == FORK_RIGHT)
        {
            return;
        }
        // If both forks are available, then the philosopher selects a fork non-deterministically.
        else if (*left_fork == FORK_AVAILABLE && *right_fork == FORK_AVAILABLE)
        {
            if (nd1())
            {
                *left_fork = FORK_RIGHT;
                return;
            }
            else
            {
                *right_fork = FORK_LEFT;
                return;
            }
        }
        // If only the left fork is available, then the philosopher will acquire the left fork.
        else if (*left_fork == FORK_AVAILABLE)
        {
            *left_fork = FORK_RIGHT;
            return;
        }
        // If only the right fork is available, then the philosopher will acquire the right fork.
        else if (*right_fork == FORK_AVAILABLE)
        {
            *right_fork = FORK_LEFT;
            return;
        }
    }
    // If the philsopher is eating, it can return to thinking and then release its forks at once.
    else if (*phil == PHIL_EATING)
    {
        *left_fork = FORK_AVAILABLE;
        *phil = PHIL_THINKING;
        *right_fork = FORK_AVAILABLE;
        return;
    }

    // Unreachable.
    assume(false);
}

// Harness to verify that:
// 1. Each philosopher can be in one of three internal states.
// 2. If a philosopher is eating, then the philosopher holds its neighbouring forks.
int main(void)
{
    // Computes interference invariant.
    int fork_1 = nd2();
    int fork_2 = nd3();
    int representative = nd4();
    int interference = nd5();
    assume(inv(fork_1, representative, fork_2));
    assume(inv(fork_2, interference, fork_1));
    tr(&fork_1, &representative, &fork_2);
    sassert(inv(fork_1, representative, fork_2));
    sassert(inv(fork_2, interference, fork_1));

    // Checks property.
    int left_fork = nd6();
    int phil = nd7();
    int right_fork = nd8();
    assume(inv(left_fork, phil, right_fork));
    sassert((phil != PHIL_EATING) || (left_fork == FORK_RIGHT && right_fork == FORK_LEFT));
    sassert(phil == PHIL_THINKING || phil == PHIL_HUNGRY || phil == PHIL_EATING);

    return 0;
}
