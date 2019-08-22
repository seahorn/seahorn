// RUN: %sea bpf -m32 -O0 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m32 -O3 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m32 -O0 --bmc=mono --horn-bv2=true --horn-bv2-lambdas --horn-vcgen-use-ite --horn-gsa --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m32 -O3 --bmc=mono --horn-bv2=true --horn-bv2-lambdas --horn-vcgen-use-ite --horn-gsa --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --horn-bv2=true --horn-bv2-lambdas --horn-vcgen-use-ite --horn-gsa --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --horn-bv2=true --horn-bv2-lambdas --horn-vcgen-use-ite --horn-gsa --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s --check-prefix=OLD
// RUN: %sea bpf -m64 -O3 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s --check-prefix=OLD

// CHECK-L: unsat
// OLD-L: sat

// Based on https://github.com/MCFuzzer/MCFuzz/issues/54.
// We get sat with the old bv-opsem.

extern void __VERIFIER_error(void) __attribute__((noreturn));

static inline unsigned int foo(unsigned int x) {
  return (x >> 24) | ((x >> 8) & 0xff00) | ((x << 8) & 0xff0000) | (x << 24);
}

unsigned int bar(unsigned long long *x) { return foo(*x); }

int main() {
  unsigned long long l = foo(0xdeadbeefU) | 0xfeedbea800000000ULL;
  if (bar(&l) != 0xdeadbeefU) {
    __VERIFIER_error();
  }
  return 0;
}
