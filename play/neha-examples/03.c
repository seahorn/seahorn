#include <assert.h>

/*
 * "nested4.c" from InvGen benchmark suite
 */


int main() {
  int i,k,n,l;


  assume(l>0);

  for (k=1;k<n;k++){
    for (i=l;i<n;i++) {
    }
    for (i=l;i<n;i++) {
        if (! 1<=i) return 42;
        //static_assert(1<=i);
    UFO: goto UFO;
    }
  }

}
