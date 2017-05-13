// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" %abc3_definitions 2>&1 | OutputCheck %s
// CHECK: ^unsat$

// Used to avoid llvm to optimize away
extern void read (int);

extern void __VERIFIER_assume (int v);
#define assume __VERIFIER_assume

extern int nd(void);

int * foo (int *c, int n, int x) {
  assume (n > 0);
  int i;
  for (i = 0; i < n; i++) 
    c[i] = x;
  return c;
}

int main() 
{
  int a[10];
  int n = nd();
  int x = nd();
  assume (n==10);
  assume (x==5);
  int *b = foo (a, n, x);
  /* int *c = foo (b, 10, 7); */
  read(b[7]);
  return 0;
}
