#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * From "Path Invariants" PLDI 07 by Beyer et al.
 */

int main(int argc, char* argv[]) {

  int i, n, a, b;
  assume( n >= 0 );
  i = 0; a = 0; b = 0;
  while( i < n ) {
    if(unknown1()) {
      a = a+1;
      b = b+2;
    } else {
      a = a+2;
      b = b+1;
    }
    i = i+1;
  }
  if (!(a+b == 3*n)) return 42;
 UFO: goto UFO;
  //static_assert( a+b == 3*n );
}
