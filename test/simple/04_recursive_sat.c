// RUN: %sea pf "%s"  2>&1 | OutputCheck %s
// CHECK: ^unsat$


#include "seahorn/seahorn.h"

int fibo(int n) {
    if (n < 1) {
        return 0;
    } else if (n == 1) {
        return 1;
    } else {
        return fibo(n-1) + fibo(n-2);
    }
}

// fibo 1-30
// 1, 1, 2, 3, 5,
// 8, 13, 21, 34, 55, 
// 89, 144, 233, 377, 610,
// 987, 1597, 2584, 4181, 6765,
// 10946, 17711, 28657, 46368, 75025,
// 121393, 196418, 317811, 514229, 832040

int main(void) {
    int x = 10;
    int result = fibo(x);
    sassert(result == 55);
    return 0;
}
