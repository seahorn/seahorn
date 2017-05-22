#include <stdio.h>


extern void __VERIFIER_error ();
extern int nd(void);

typedef int(*fn_t)(int);

int foo(int v){ __VERIFIER_error (); return v;}

__attribute__((always_inline)) void assert (int v) { if (!v) __VERIFIER_error (); }

extern void use (fn_t fn);

int bar(int v) {return v+1;}

extern void* ndfn(void);

int test1(int x){return x*2;}

int test2(int x){
    if (x<0) __VERIFIER_error();
    return x/2;

}

int test3(){

	float y = 0.1;
	while (y != 1.1) {
            printf("x = %f\n", y);
            y = y + 0.1;
	}
	//unreachable
	return 0;
    }



int test4 ()
{
    int SIZE = 10;
    int a[SIZE];

    int j=SIZE;
    int done=0;

    do
    {
        j--;
        if (a[j]==nd()) {
            assert(0<=j);
            done = 1;
        }
    } while ( done==0 && j >= 0 );

    return done;
}

int main(void)
{

  fn_t fn;
  int x = nd();

  x = bar(x);
  use(&foo);
  fn = (fn_t)ndfn ();
  fn(x);
  test1(x);
  test2(x);
  test3();
  test4();
  return 42;
}
