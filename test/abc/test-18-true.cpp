// RUN: %sea abc -O3 --lower-invoke --symbolize-constant-loop-bounds --simplify-pointer-loops --abc-encoding=%abc_encoding %dsa --abc-escape-ptr "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include <vector>

extern "C" int nd();
extern "C" void do_something(int x);
extern "C" void __VERIFIER_assume(int);
#define assume __VERIFIER_assume

int main() {

  int n = nd();
  assume(n > 0);

  std::vector<int> a;
  for (unsigned int i = 0; i < n; i++) {
    a.push_back(77);
  }

#ifndef SHORT
  for (std::vector<int>::iterator it = a.begin(), et = a.end(); it != et;
       ++it) {
    do_something(*it);
  }
#endif

  return 42;
}
