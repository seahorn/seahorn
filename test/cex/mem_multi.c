// RUN: %solve --horn-bmc-engine=mono --horn-bv2-extra-widemem --horn-bv2-lambdas=false --horn-bmc --horn-bv2=true --keep-shadows=true --cex=/tmp/multi.ll %s > /dev/null 2>&1
// RUN: %cex --run -g %s /tmp/multi.ll 2>&1 | OutputCheck %s

// CHECK: ^__VERIFIER_error was executed$

#include <stddef.h>
#include "seahorn/seahorn.h"
extern void memhavoc(void *ptr, size_t size);

int main(void) {
	int nums[5];
	memhavoc(nums, sizeof(nums));
	int nums2[2];
	memhavoc(nums2, sizeof(nums2));
	int x = nums[2];
	int y = nums2[0];
	if (x > 10) {
		y = x;
	}
	sassert(y == x);
}
