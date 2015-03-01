#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Adapted from ex17.c in NECLA test suite
 */

int main(int flag, int a) {
   int b;
   int j = 0;

   for (b=0; b < 100 ; ++b){
      if (flag)
         j = j +1;
   }


   if(flag)
      static_assert(j==100);
}
