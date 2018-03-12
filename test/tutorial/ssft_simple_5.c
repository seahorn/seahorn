// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// CHECK: ^unsat$

int unknown(void);
int unknown1(void);

extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
void assert (int v) { if (!v) __VERIFIER_error (); }


#define assume __VERIFIER_assume
#define static_assert assert

int main(void) {
  int c1 = 4000;
  int c2 = 2000;
  int n, v;
  int i, k, j;


  n = unknown();
  assume(n>0);
  assume(n<10);


  k = 0;
  i = 0;
  while( i < n ) {
    i++;
    if(unknown1() % 2 == 0)
      v = 0;
    else v = 1;

    if( v == 0 )
      k += c1;
    else
      k += c2;
  }

  static_assert(k>n);
  return 0;
}
