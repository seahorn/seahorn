// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// RUN: %shorntest %t-harness0.ll %t-debug0 %s -O0 | OutputCheck %s
// RUN: %shorntest %t-harness1.ll %t-debug1 %s -O1 | OutputCheck %s
// RUN: %shorntest %t-harness2.ll %t-debug2 %s -O2 | OutputCheck %s
// RUN: %shorntest %t-harness3.ll %t-debug3 %s -O3 | OutputCheck %s
// CHECK: ^unsat$

#define sassert(X)                                                             \
  if (!(X))                                                                    \
  __VERIFIER_error()

extern int nd(void);

/* Global ghost variable. Keeps the state of the lock. */
int g_lock = 0;

__attribute__((always_inline)) void lock(void) {
  /* stub modeling the lock function */
  sassert(!g_lock);
  g_lock = 1;
}

__attribute__((always_inline)) void unlock(void) {
  /* stub modeling the unlock function */
  sassert(g_lock);
  g_lock = 0;
}

int main(void) {
  int request, old, total;

  total = nd();
  request = 0;
  do {
    lock();
    old = total;
    request = nd();
    if (request) {
      unlock();
      total = total + 1;
    }
  } while (total != old);

  unlock();

  return 0;
}