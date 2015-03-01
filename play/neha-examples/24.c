#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * "nested5.c" from InvGen test suite
 */

void main() {
  int i,j,k,n;
  
  for (i=0;i<n;i++)
    for (j=i;j<n;j++)
      for (k=j;k<n;k++)
	static_assert(k>=i);
}
