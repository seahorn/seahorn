#define STEPS 3

extern int nd(void);
extern void __VERIFIER_error(void) __attribute__((noreturn));
#define sassert(X) (void)(!!(X) || __VERIFIER_error())

struct B { B *next; };
struct S : B { int val; S(B* n, int v) : B{n}, val(v) {} }; 

int main() {
  B b1 = {&b1};
  S s2 = {&b1, '2'};
  S s3 = {&s2, '3'};

  B *ptr = &s3;
  for (int i = 0; i < STEPS; ++i)
    ptr = ptr->next;

  sassert(ptr + __offsetof(S::val) < ptr + sizeof(B));
  return ((S *) ptr)->val;
}