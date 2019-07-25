// RUN: %sea bpf -m64 -O0 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s

// CHECK-L: unsat
// XFAIL: *

// Based on https://github.com/MCFuzzer/MCFuzz/issues/45.
// We get sat with the old bv-opsem.

extern void __VERIFIER_error(void) __attribute__((noreturn));

int array[6] = {1, 2, 3, 4, 5, 6};

int main() {
  for (int i = 0; i < 5; i++)
    array[i] = 0;
  if (array[5] != 6)
    __VERIFIER_error();
  return 0;
}
