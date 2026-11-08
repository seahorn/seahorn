// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

extern int nd ();

int main ()
{
  int x = 0;
  
  while (x<nd()) {
  	x+=2;
  }

  if (x == 1) {
  	//unreachable
  	return 0;
  }

  return x;
}
