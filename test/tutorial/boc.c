// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// RUN: %shorntest %t-harness0.ll %t-debug0 %s --horn-use-mbqi -O0 | OutputCheck %s
// RUN: %shorntest %t-harness1.ll %t-debug1 %s --horn-use-mbqi -O1 | OutputCheck %s
// RUN: %shorntest %t-harness2.ll %t-debug2 %s -O2 | OutputCheck %s
// RUN: %shorntest %t-harness3.ll %t-debug3 %s -O3 | OutputCheck %s
// CHECK: ^unsat$

/**
 * Check whether main() has a buffer overflow.
 *
 * Produce a counterexample. Correct. Verify your correction.

 * Commands to use:
 *
 * # compile
 * sea clang -S -o queue.ll queue.c
 * # instrument with buffer-overflow checks (BOC)
 * sea pp --boc -S -q queue.boc.ll queue.ll
 * # verify
 * sea pf --cex=trace.xml --inline queue.boc.ll 2>&1 | q.log
 *
 * See q.log for a counterexample and the program being verified
 **/

#define sassert(X)                                                             \
  if (!(X))                                                                    \
  __VERIFIER_error()

extern int nd();
#define SZ 16

int a[SZ];

int main(void) {
  int x = nd();
  signed low = 0, high = SZ;

  while (low < high) {
    signed middle = low + ((high - low) / 2);
    sassert(0 <= middle && middle < SZ);

    if (a[middle] < x)
      high = middle;
    else if (a[middle] > x)
      low = middle + 1;
    else /* a [middle] == x ! */
      return middle;
  }
  return -1;
}
