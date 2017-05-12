// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

int main() 
{
  int i;
  char a[10];
  for (i = 0; i < 10; i++) 
  {
    a[i] = 89;
  }
  return a[i-1];
}
