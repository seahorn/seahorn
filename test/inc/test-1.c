// RUN: %sea_inc --null --num-blks=2 "%s" 2>&1 | OutputCheck %s
// CHECK: INFEASIBLE

// This test can only pass if line 349 in tools/seapp/seapp.cc
//    pass_manager.add (llvm::createGlobalOptimizerPass());
// is commented out.

#include <stdio.h>

extern int nd();
extern void __VERIFIER_error(void);
#define assert(c)                                                              \
  if (!c)                                                                      \
    __VERIFIER_error();

typedef struct example_s {
  struct example_s *bases;
  const char *repr;
} example;

#define hashCode(this) ((size_t)this->bases)

int example3(example *o) {
  if (o != NULL) {
    return hashCode(o);
  }
  printf("%s does not exist\n", o->repr);
  return 2;
}
