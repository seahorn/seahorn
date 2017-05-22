// RUN : sea_inc ../play/inconsistency/unit_test.c --null --num-blks 3
// EXPEXT : All infesaible

#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>

extern int nd ();
extern void __VERIFIER_error (void);
#define assert(c) if (!c) __VERIFIER_error ();

typedef struct example_s {
	struct example_s* bases;
	const char* repr;
} example;

#define hashCode(this) ((size_t) this->bases)

#define EX1
#define EX2 
#define EX3
#define EX4
#define EX6
#define EX7
#define EX8 
#define EX9 

#ifdef EX0
/// XXX: Clang gets rid of "result = result / 0;" so there is no way
/// to find the inconsistency at the bitcode level.
void example0(int c, int d){
 const int i = 0;
 int result = c+d;
 if (i>0){
    result = result / 0;
 }
}
#endif

#ifdef EX1
// Run with --null
// We miss the inconsistency because we find three paths that visit
// all basic blocks even if blocks A and B are inconsistent with each
// other.
bool example1(example* this, const example* other) {

	if (this->bases == NULL) {
            if (other->bases != NULL) {
              return false;
            } // A: here we know that this->base==other->base==NULL
	}

	if (hashCode(this->bases) != hashCode(other->bases)) { //inconsistent with 17
            // B 
            printf ("this is inconsistent!\n");
            return false;
	}

  return true;
}
#endif

#ifdef EX2
// Run with --boa
// XXX: We find the inconsistency but
//      sometimes I get TIMEOUT! this should not happen ....
int example2(int n) {
  int arr[n];
  arr[3] = 3;
  return arr[n]; // Inconsistent with 28
}
#endif

#ifdef EX3
// Run with --null
// XXX: We find the inconsistency
int example3(example* o) {
  if (o != NULL) {
    return hashCode(o);
  }
  printf("%s does not exist\n", o->repr); //inconsistent with line 34
  return 2;
}
#endif

#ifdef EX4
// Run with --boa
//
// XXX: It seems that Seahorn does not terminate. Using large block
// encoding SeaHorn works as expected. Need to debug more ....
void example4(int n) {
	int arr[n];
	int i;
	for (i=0; i<=n; i++) {
	  arr[i]=i; // inconsistent off by one
            // XXX do something with arr[i] otherwise trivial dead
            // code elimination will remove it
            //
            // XXX this is not enough because llvm replaces arr[i]
            //     with i so arr[i] is still removed:
            //printf("%d\n", arr[i]);
            if (nd ()) printf("%d\n", arr[i]);
          }
}
#endif

#ifdef EX5
// XXX: seahorn does not instrument division instructions so nothing
// will be detected here
void example5(int a, int b) {
  b=1; // all inconsistent: div by zero
	if (a>0) b--;
  b=1/b;
	if (a<=0) b=1/(1-b);
}
#endif

#ifdef EX6
// Run with --null
//
// XXX: we cannot find the inconsistency because "if (o == NULL)" is
// not used as a condition in a branch by llvm. So we cannot find
// an inconsistency between blocks.
//
// "if (o == NULL) { ... return false; }" is simply translated by LLVM to:
//
// %r = icmp ne o NULL;
// return %r
// Update: with option -horn-one-assume-per-block we find the inconsistency
bool example6(example* o) {
  printf("%s\n", o->repr);
  if (o == NULL) {
    printf("this is inconsistent!\n");
    return false; // inconsistent wrt 57
  }
  return true;
}
#endif

#ifdef EX7
// Run wiht --boa
// XXX: We find the inconsistency
int example7(int arr[]) {
	return arr[-1]; // inconsistent
}
#endif

#ifdef EX8
// XXX: here we cannot find the inconsistency because of the same
// reason described in EX6
int example8(int length) {
  char temp[length];
  int repos = -1;
  int end = -1;
  int j = end;
  do {
    j++;
    assert (j < length);
    if (temp[j]=='a') {
      repos = j - end - 1;
    }
  } while (repos == -1 && j < length);
  if (repos == -1) {
    repos=0; //unreachable
  }
  return repos;
}
#endif


#ifdef EX9
// We need to run with option --single because the inconsistency
// requires interprocedural reasoning.
int getInt(int n) {
   return 0;
}

int example9(int index, int ints_size, int chars_size, int bytes_size, int booleans_size) {
	int max = 0;
	if (booleans_size > 0 && index < 63)
		max = 64;
	else if (bytes_size > 0 && index < 56)
		max = 57;
	else if (chars_size > 0 && index < 48)
		max = 49;
	else if (ints_size > 0 && index < 32)
		max = 33;

	if (max != 0) {
		int rand = getInt(4);
		max = max - index;
		//at this point, max must be 1 because
		//if max!=0, then one of the cases above
		//was taken s.t. max is always set to index+1
		// hence the line above always sets index to 1
                    //
                    // XXX: this is not true!!!!!
                    ///     max is not always index+1 because the above conditions are
                    ///     index < 63 rather than index == 63, ....
		if (max > rand)
			max = rand;
		else if (max != 1)
			max = getInt(max); // unreachable
		index+=max;
	}
	return index;
}
#endif
