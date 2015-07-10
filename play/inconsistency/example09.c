//from wikipedia

#include <stdio.h>

int main(void)
{
   int a = 0;
   while (a < 10) {
      printf("%d\n", a);
      if (a = 5)
         printf("a equals 5!\n");
      a++;
   }
   //unreachable
   return 0;
}