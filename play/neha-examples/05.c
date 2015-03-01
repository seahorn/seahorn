#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

int main(int flag)
{

	int x = 0;
	int y = 0;

	int j = 0;
	int i = 0;


	while(unknown1())
	{
	  x++;
	  y++;
	  i+=x;
	  j+=y;
	  if(flag)  j+=1;
	}
        if (! (j>=i)) return 42;
 UFO: goto UFO;
	//static_assert(j>=i);

}
