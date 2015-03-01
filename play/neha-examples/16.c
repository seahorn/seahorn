#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();


/*
 * From "A Practical and Complete Approach to Predicate Refinement" by McMillan TACAS'06
 */

int main(int i, int j) {
  
  int x = i;
  int y = j;
 
  while(x!=0) {
	x--;
	y--;
  }
  if(i==j)
	static_assert(y==0);
}

