// RUN: %sea bpf -m64 -O0 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s

// CHECK-L: unsat
// XFdAIL: *

// Based on https://github.com/MCFuzzer/MCFuzz/issues/53.
// With the old bv-opsem we get sat.

extern void __VERIFIER_error(void) __attribute__((noreturn));

int f(int *p, int *x) {
  *p++;
  *x++;
  *x = *p;
  return 0;
}

int main() {
  int u[2] = {123, 234};
  int x[2] = {17689, 23456};
  f(u, x);
  if (x[1] != 234) {
    __VERIFIER_error();
  }
  return 0;
}
