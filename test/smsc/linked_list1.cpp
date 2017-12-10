#define STEPS 3

struct B { B *next; };
struct S : B { int val; S(B *n, int v) : B{n}, val(v) {} }; 

int main() {
  B b1 = {&b1};
  S s2 = {&b1, '2'};
  S s3 = {&s2, '3'};

  B *ptr = &s3;
  for (int i = 0; i < STEPS; ++i)
    ptr = ptr->next;

  return ((S *) ptr)->val;
}
