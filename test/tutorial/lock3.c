// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// RUN: %shorntest %t-harness0.ll %t-debug0 %s -O0 | OutputCheck %s
// RUN: %shorntest %t-harness1.ll %t-debug1 %s -O1 | OutputCheck %s
// RUN: %shorntest %t-harness2.ll %t-debug2 %s -O2 | OutputCheck %s
// RUN: %shorntest %t-harness3.ll %t-debug3 %s -O3 | OutputCheck %s
// CHECK: ^unsat$

extern int nd(void);
extern void *nd_lock(void);

extern void __VERIFIER_error(void) __attribute__((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int v) __attribute__((__always_inline__)) {
  if (!v)
    __VERIFIER_error();
}

#define assert __VERIFIER_assert
#define assume __VERIFIER_assume

/* Global ghost variable. Keeps the state of the lock stored in g_lock. */
int g_lock_cnt = 0;
/* Global lock being checked */
void *g_lock;

__attribute__((always_inline)) void lock(void *lck) {
  /* stub modeling the lock function */
  if (lck == g_lock) {
    /* only track the property the given lock is currently tracked */
    assert(!g_lock_cnt);
    g_lock_cnt = 1;
  }
}

__attribute__((always_inline)) void unlock(void *lck) {
  /* stub modeling the unlock function */
  if (lck == g_lock) {
    /* only track the property the given lock is currently tracked */
    assert(g_lock_cnt);
    g_lock_cnt = 0;
  }
}

int main(void) {
  /* choose a lock to be tracked by the analysis */
  g_lock = nd_lock();

  /* two locks. Addresses of the variables are used as lock ids */
  int lck1;
  int lck2;

  lock(&lck1);
  unlock(&lck1);
  lock(&lck2);
  unlock(&lck2);

  /** all locks are released at the end */
  assert(g_lock_cnt == 0);
  return 0;
}