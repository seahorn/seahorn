extern void __VERIFIER_error ();
extern int nd(void);

typedef int(*fn_t)(int);

int foo(int v){ __VERIFIER_error (); return v;}
extern void use (fn_t fn);

int bar(int v) {return v+1;}

extern void* ndfn(void);

int main(void)
{
  
  fn_t fn;
  int x = nd();

  x = bar(x);
  use(&foo);
  fn = (fn_t)ndfn ();
  fn(x);
  
  return 42;
}
