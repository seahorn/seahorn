// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// RUN: %shorntest %t-harness0.ll %t-debug0 %s -O0 | OutputCheck %s
// RUN: %shorntest %t-harness1.ll %t-debug1 %s -O1 | OutputCheck %s
// RUN: %shorntest %t-harness2.ll %t-debug2 %s -O2 | OutputCheck %s
// RUN: %shorntest %t-harness3.ll %t-debug3 %s -O3 | OutputCheck %s
// CHECK: ^unsat$

/**
 * Check whether main() has a buffer overflow.
 **/

#define sassert(X)                                                             \
  if (!(X))                                                                    \
  __VERIFIER_error()
extern int nd(void);
#define N 4

int buf[N];
int hi = 0;
int lo = 0;
int size = N;

void enqueue(int x) {
  buf[hi] = x;
  hi = (hi + 1);
}

int dequeue() {
  int res = buf[lo];
  lo = (lo + 1);
  return res;
}

int main(void) {
  while (nd()) {
    if (nd()) {
      int x = nd();
      enqueue(x);
    } else
      dequeue();
  }
  return 0;
}