#include <stdio.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
__attribute__((always_inline)) void assert (int v) { if (!v) __VERIFIER_error (); }
int __VERIFIER_nondet_int();

main()
{
    unsigned int SIZE=1;
    unsigned int j,k;
    int array[SIZE], menor;

    menor = __VERIFIER_nondet_int();

    for(j=0;j<SIZE;j++) {
        array[j] = __VERIFIER_nondet_int();

        if(array[j]<=menor)
            menor = array[j];
    }

    assert (array[0]>=menor);
    printf("OLA");
}
