// RUN: %sea pf "%s"  2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include "seahorn/seahorn.h"

int main() {
  int x = 0, y = 1, z = 2;

  sassert(x == 0);
  //  Check if sassert works with the comma operator.
  while (sassert(y == 1), 0)
    ;

  if (z > 0)
    sassert(z > 1);
  else // Ensure that sassert doesn't 'hijack' the next else statement.
    sassert(z < 1); // This else is supposed to be dead.

  sassert(y >= 1 && (0, !x)); // Check if sassert handles commas in conditions.
}
