#include <stdio.h>
#include <assert.h>

void __VERIFIER_error() {
  printf("__VERIFIER_error was executed\n");
  exit(1);
}

void __VERIFIER_assume(int x) {
  assert(x);
}
