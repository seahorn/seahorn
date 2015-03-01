#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

void main()
{
  int x = 0;
  int y = 0;
  int z = 0;
  int k = 0;

  while(unknown1())
  {
     if(k%3 == 0)
       x++;
     y++;
     z++;
     k = x+y+z;
  }

  static_assert(x==y);
  static_assert(y==z);
 
}

