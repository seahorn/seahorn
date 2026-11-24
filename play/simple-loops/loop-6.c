// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

int main(){
  int i=0;  
  int j=0;
  while (i <= 100){
    while (j <= 100){
      j++;
    }
    i++;
  }        
  return i+j;  
}
