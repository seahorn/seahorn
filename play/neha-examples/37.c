#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Taken from "Counterexample Driven Refinement for Abstract Interpretation" (TACAS'06) by Gulavani
 */

void main(int n) {
  int x= 0;
  int m=0;
  while(x<n) {
     if(unknown1()) {
	m = x;
     }
     x= x+1;
  }
  if(n>0) static_assert(0<=m && m<n);
}
