// RUN: %sea --add-branch-sentinel --eval-branch-sentinel "%s" 2>&1 | OutputCheck %s
// CHECK-NOT: ^Info: Conditional branch became true
// CHECK-NOT: ^Info: Conditional branch became false

#include <stddef.h>

extern int nd_int(void);

int main() {
  size_t a = nd_int();
  size_t b;
  if (a == 0) {
    b = 1;
  } else {
    b = 0;
  }
  return 0;
}
  
