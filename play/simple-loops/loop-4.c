// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

int  main() {
  int z;
  int i = 0, j = 0;
  while (i < 10) {
    i++;
    j = 2 * i;
  }  
  z = i+j;
  return z;
}
