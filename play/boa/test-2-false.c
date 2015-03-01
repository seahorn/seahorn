#include <stdio.h>
int main(int argc, char**argv) 
{
  int i;
  int a[10];
  for (i = 0; i < 10; i++) 
  {
    a[i] = i;
  }
  printf("%d\n", a[i]);
  return 42;
}
