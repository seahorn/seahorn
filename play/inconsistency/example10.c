// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

//from wikipedia

#include <stdio.h>

int main(void)
{
	float x = 0.1;
	while (x != 1.1) {
	  printf("x = %f\n", x);
	  x = x + 0.1;
	}
	//unreachable
	return 0;
}
