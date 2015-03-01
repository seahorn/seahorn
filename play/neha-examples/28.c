#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();


/*
 * From CAV'12 by Sharma et al.
 */

void main() {
  int x=0;
  int y=0;
  int n = 0;
  while(unknown()) {
      x++;
      y++;
  }
  while(x!=n) {
      x--;
      y--;
  }
  static_assert(y==n);
}
