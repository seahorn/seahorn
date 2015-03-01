#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Based on ex3 from NECLA Static Analysis Benchmarks
 */


void main()
{
  int j=0;
  int i;
  int x=100;
   
   
  for (i =0; i< x ; i++){
    j = j + 2;
  }

  static_assert(j == 2*x);
}


