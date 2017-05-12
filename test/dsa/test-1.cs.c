// RUN: %sea fe-inspect -O0 %cs_dsa --mem-dot %s --dot-outdir=%T/test-1.cs.c
// RUN: %cmp-graphs %tests/test-1.cs.c.main.mem.dot %T/test-1.cs.c/main.mem.dot | OutputCheck %s -d
// CHECK: ^OK$

extern int nd ();
void f ( int *x , int *y ) {
  *x = 1 ; *y = 2 ;
}

void g (int *p , int *q , int *r , int *s) {
  f (p,q) ;
  f (r,s);
}

int main (int argc, char**argv){

  int x;
  int y;
  int w;
  int z;

  int *a = &x;
  int *b = &y;
  if (nd ()) a = b;
  
  g(a, b, &w, &z);
  return x + y + w + z;
}
