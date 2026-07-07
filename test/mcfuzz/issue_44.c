// RUN: %sea bpf -m32 -O0 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | filecheck %s
// RUN: %sea bpf -m32 -O3 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | filecheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | filecheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | filecheck %s

// CHECK: unsat
// UNSUPPORTED: true

// Based on https://github.com/MCFuzzer/MCFuzz/issues/46.
// Historically XFAIL: both bv-opsems gave sat. On dev16 the verdict is
// environment-dependent (unsat in the local jammy-llvm16 container, fail on
// the CI runner), so neither XFAIL nor plain pass is stable; disabled.

extern void __VERIFIER_error(void) __attribute__((noreturn));

struct s {
  int a : 16, b;
};

struct s f(struct s x) {
  x.b = 1;
  return x;
}

int main() {
  struct s i;
  i.a = 2;
  i = f(i);
  if (i.a != 2)
    __VERIFIER_error();
  return 0;
}