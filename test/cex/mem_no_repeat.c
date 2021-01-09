// RUN: %solve --horn-bmc-engine=mono --horn-bv2-extra-widemem --horn-bv2-lambdas=false --horn-bmc --horn-bv2=true --keep-shadows=true --cex=/tmp/no_rpt.ll %s > /dev/null 2>&1
// RUN: %cex --run -g %s /tmp/no_rpt.ll 2>&1 | OutputCheck %s

// CHECK: ^__VERIFIER_error was executed$

#include <stddef.h>
#include "seahorn/seahorn.h"
extern void memhavoc(void *ptr, size_t size);
extern size_t nd_int(void);

int main(void) {
	int nums[5];
	memhavoc(nums, sizeof(nums));
	int x = nums[0];
	int y = 0;
	if (nd_int()) {
		y = x;
	} else {
		y = nums[4];
	}
	sassert(y == x);
}
