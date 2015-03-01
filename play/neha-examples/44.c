#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Adapted from ex20 from NECLA Static Analysis Benchmarks
 */


int main(int k, int flag)
{
  int i=0;
  int j=0;
  int n;
  int __BLAST_NONDET;


  if (flag == 1){
     n=1;
  } else {
     n=2;
  }

  i=0;

  while ( i <= k){
    i++;
    j= j +n;
  }
  if(flag == 1)
      static_assert(j == i);
	
}


