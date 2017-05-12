// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^sat$

extern int nd ();

int main() 
{
  int i;
  char a[10];
  for (i = 0; i < 10; i++) 
  {
    a[i] = 89;
  }
  // trick llvm so that it cannot detect overflow
  return a[nd()>0?i:i+1];
}
