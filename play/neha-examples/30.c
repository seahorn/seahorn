#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Based on "SYNERGY: A New Algorithm for Property Checking" by Gulavani et al.
 */

int main() {

  int i, c;
  i = 0;
  c = 0;
  while (i < 1000) {
    c = c + i;
    i = i + 1;
  }

  static_assert(c>=0);
}

