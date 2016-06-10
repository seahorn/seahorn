#include "seahorn.h"

int nd();
int nd1();

int main() {
   int j = 2;
   int k = 0;

   while(nd()){
       if (nd1())
       j = j + 4;
     else {
       j = j + 2;
       k = k + 1;
     }
   }
   if(k!=0)
     sassert(j==2*k+2);
   return 0;
}
