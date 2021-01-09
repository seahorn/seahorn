// RUN: %solve --horn-bmc-engine=mono --horn-bv2-extra-widemem --horn-bv2-lambdas=false --horn-bmc --horn-bv2=true --keep-shadows=true --cex=/tmp/mem_nd_size.ll %s > /dev/null 2>&1
// RUN: %cex --run -g %s /tmp/mem_nd_size.ll 2>&1 | OutputCheck %s

// CHECK: ^__VERIFIER_error was executed$


#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>
#include "seahorn/seahorn.h"
extern void memhavoc(void *ptr, size_t size);
extern size_t nd_int(void);
extern bool nd_bool(void);

int main(void) {
	size_t len = nd_int();
	assume(len < 5);
	int *nums;
	nums = malloc(len * sizeof(*nums));
	memhavoc(nums, len * sizeof(*nums));
	size_t i = nd_int();
	assume(i < len);
	int x = nums[i];
	int y = 0;
	if (x > 10 && nd_bool()) {
		y = x + 5;
	}
	sassert(y == 0);
	free(nums);
}
