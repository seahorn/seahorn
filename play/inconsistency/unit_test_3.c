#include <stddef.h>
#include <stdio.h>

extern int nd();

// This function is inconsistent between A and B using --null
// However, we miss the inconsistency because its corresponding
// bitcode is:
//
//  %1 = icmp eq i32* %x, null
//  %.i = select i1 %1, i32 1, i32 %i
//  %null_check1 = icmp ne i32* %x, null
//  call void @verifier.assume(i1 %null_check1)
//  
//  we now that .i cannot be 1 becuase %1 and %null_check1 contradicts
//  each other but everything is happenning in the same basic block so
//  our algorithm cannot detect the inconsistency.
void test01(int *x, int i) {
    if (x == NULL) {
        i = 1; //A
    }
    *x = i; // B
}

// This function is inconsistent between A and B using --null
// Same than test01 but with an extra instruction. 
// We can now catch the inconsistency because llvm generates two blocks!
void test02(int *x, int i) {
    if (x == NULL) {
        i = 1; //A
        printf("lebron sucks!\n");
    }
    *x = i; // B
}


// This function is inconsistent between A and B with --null
// We miss the inconsistency becase A and B are in the same llvm basic block.
void test03(int *x, int i) {
  *x = i ; // A
  if (x== NULL) {
    // B
    i = 1;
  }
}

