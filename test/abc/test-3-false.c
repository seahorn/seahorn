// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^sat$

// Used to avoid llvm to optimize away
extern void read (int);

extern int nd ();

int a[10];

// To test loops 
int main(int argc, char**argv) 
{
  int i;

  for (i = 0; i < 10; i++) {
    a[i] = i;
  }
  // trick llvm so that it cannot detect overflow
  read(a[(nd()>0?i-1:i)]);
  return 0;
}
