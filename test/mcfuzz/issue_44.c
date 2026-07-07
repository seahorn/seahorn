// RUN: %sea bpf -m32 -O0 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | filecheck %s
// RUN: %sea bpf -m32 -O3 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | filecheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | filecheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | filecheck %s

// CHECK: unsat

// Based on https://github.com/MCFuzzer/MCFuzz/issues/46.
// Historically XFAIL: both the old and new bv-opsem gave sat. Passes on
// dev16 (LLVM 16 + IndVarSimplify enabled on the bounded flows).

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