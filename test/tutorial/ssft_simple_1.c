// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// CHECK: ^unsat$

int unknown1(void);

/*
 * from Invgen test suite
 */

extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
void assert (int v) { if (!v) __VERIFIER_error (); }

#define assume __VERIFIER_assume
#define static_assert assert

int main(void) {

    int n, k, j;


    n = unknown1();
    assume(n>0);

    k = unknown1();
    assume(k>n);
    j = 0;
    while( j < n ) {
        j++;
        k--;
    }
    static_assert(k>=0);
    return 0;
}
