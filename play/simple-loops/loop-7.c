// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

int main() {
  int i, j;
  for (i=0; i<5; i++)
    for(j=5; j>=0; j--);
  return i+j;
}
