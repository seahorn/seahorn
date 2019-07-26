// RUN: %sea bpf -m32 -O0 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m32 -O3 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s

// CHECK-L: unsat
// XFAIL: *

// Based on https://github.com/MCFuzzer/MCFuzz/issues/41.
// Incorrect with both old and new bv-opsem.

extern void __VERIFIER_error(void) __attribute__((noreturn));

void foo() {
  static int last_align = -1;
  int dummy = 0;
  int align = (int)&dummy & 15;
  if (last_align < 0)
    last_align = align;
  else if (align != last_align) {
    __VERIFIER_error();
  }
}

int main() {
  foo();
  foo();
  return 0;
}
