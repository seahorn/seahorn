// RUN: %sea --add-branch-sentinel --eval-branch-sentinel "%s" 2>&1 | OutputCheck %s
// CHECK: ^Info: Conditional branch became false

#include <stddef.h>

int main() {
  size_t a = 0;
  size_t b;
  if (a > 0) {
    b = 1;
  } else {
    b = 0;
  }
  return 0;
}
  
