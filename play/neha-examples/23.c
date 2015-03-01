#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * ex49 from NECLA Static Analysis Benchmarks
 */


int main( int n){
   int i, sum=0;
   assume( n >= 0);

   for (i=0; i < n; ++i)
      sum = sum +i;

   static_assert(sum >= 0);
}

