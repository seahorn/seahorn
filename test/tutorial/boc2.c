// RUN: %shorntest %t-harness.ll %t-debug %s | OutputCheck %s
// RUN: %shorntest %t-harness0.ll %t-debug0 %s -O0 | OutputCheck %s
// RUN: %shorntest %t-harness1.ll %t-debug1 %s -O1 | OutputCheck %s
// RUN: %shorntest %t-harness2.ll %t-debug2 %s -O2 | OutputCheck %s
// RUN: %shorntest %t-harness3.ll %t-debug3 %s -O3 | OutputCheck %s
// CHECK: ^unsat$

/** Convert this program into SSA **/
int nd(void);
char *ndc(void);

extern void __VERIFIER_error(void);
int main(void) {
  int i;
  char *buf;
  char last;

  i = nd();
  buf = ndc();

  if (buf[i] == '\0') {
    int start = 0;
    while (start < i) {
      buf[start] = 'f';
      start++;
      last = buf[start - 1];
    }
    if (start > 1 && last != 'f')
      __VERIFIER_error();
  }
  return 0;
}