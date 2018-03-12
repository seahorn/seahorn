// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// CHECK: ^unsat$

int unknown(void);
int unknown1(void);

/*
 * "nest-if8" from InvGen benchmark suite
 */


extern void __VERIFIER_error (void);
void assert (int v) { if (!v) __VERIFIER_error (); }

#define static_assert assert

int main(void) {
  int i,j,k,n,m;
  i = unknown();
  j = unknown();
  n = unknown();
  m =  unknown();

  if( m+1 < n );
  else return 0;
  for ( i=0; i<n; i+=4 ) {
    for ( j=i; j<m; ) {
      if (unknown1()){
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
