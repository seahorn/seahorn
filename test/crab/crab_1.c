// RUN: %sea pf --max-depth=20 --crab --crab-dom=int "%s" 2>&1 | OutputCheck %s
// CHECK: ^unsat$

// Without --crab seahorn should not terminate.

extern int nd(void);
extern void __VERIFIER_error(void) __attribute__((noreturn));
#define assert(X)                                                              \
  if (!(X)) {                                                                  \
    __VERIFIER_error();                                                        \
  }

int main() {
  int x, y;
  x = 1;
  y = 0;
  while (nd()) {
    x = x + y;
    y++;
  }
  assert(x >= y);
  return 0;
}
