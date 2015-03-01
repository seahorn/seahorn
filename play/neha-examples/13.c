#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Based on "Property-Directed Incremental Invariant Generation" by Bradley et al.
 */

int main(int flag) {
   int j = 2; 
   int k = 0;

   while(unknown1()){ 
     if (flag)
       j = j + 4;
     else {
       j = j + 2;
       k = k + 1;
     }
   }
   if(k!=0)
     static_assert(j==2*k+2);
}
