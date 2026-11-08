// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

//from wikipedia

#include <stdio.h>

int main(void)
{
	int SIZE = 10;
	int a[SIZE];
	for (int i=0; i<SIZE; i++) {
		a[i] = i;
	}

	int key = 200;
	for (int i=0; i<SIZE; i++) {
		if (a[i]==key) {
			//unreachable
			return key;
		}
	}

	return 0;
}