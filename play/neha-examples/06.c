#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

int main()
{


  int w = 1;
  int z = 0;
  int x= 0;
  int y=0;

  while(unknown1()){

    while(unknown2()){
      if(w%2 == 1) x++;
      if(z%2==0) y++;
    }
    z=x+y;
    w=z+1;
  }

  if (! (x==y)) return 42;
 UFO: goto UFO;
  //static_assert(x==y);
}
