// If the multidimensional array is local then LLVM generates multiple
// GetElementPtr instructions

int main(int arg, char **argv){
  int p[2][2][2];

  p[0][0][0] = 1;
  p[0][0][1] = 1;
  p[0][1][0] = 1;
  p[0][1][1] = 1;
  p[1][0][0] = 1;
  p[1][0][1] = 1;
  p[1][1][0] = 1;
  p[1][1][1] = 1;
  return 42;
}
