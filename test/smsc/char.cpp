#define STEPS 3

extern int nd(void);

int main() {
  int x = nd();
  char *c = (char *) &x;
  char *d = c;
  for (int i = 0; i < STEPS; ++i) ++d;
  *d = 'a';
  return x;
}
