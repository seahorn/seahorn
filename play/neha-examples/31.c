
#include <assert.h>
int unknown1();

/*
 * "nest-if8" from InvGen benchmark suite
 */


int main() {
  int i,j,k,n,m;
  if( m+1 < n ); else return;
  for ( i=0; i<n; i+=4 ) {
    for ( j=i; j<m; ) {
      if (unknown1()){
        static_assert( j >= 0 );
        j++;
        k = 0;
        while( k < j ) {
          k++;
        }
      }
      else { 
	static_assert( n+j+5>i );
	j+= 2;
      }
    }
  }
}
