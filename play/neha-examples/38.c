#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

void main(int n)
{
  int x=0;
  int y=0;
  int i=0;
  
  while(i<n) {
    i++;
    x++;
    if(i%2 == 0) y++;
  }
  
  if(i%2 == 0) static_assert(x==2*y);
}

