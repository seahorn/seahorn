// RUN: %sea bpf -m32 -O0 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m32 -O3 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m32 -O0 --bmc=mono --horn-bv2=true --horn-bv2-lambdas --horn-vcgen-use-ite --horn-gsa --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m32 -O3 --bmc=mono --horn-bv2=true --horn-bv2-lambdas --horn-vcgen-use-ite --horn-gsa --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --horn-bv2=true --horn-bv2-lambdas --horn-vcgen-use-ite --horn-gsa --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --horn-bv2=true --horn-bv2-lambdas --horn-vcgen-use-ite --horn-gsa --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s


// CHECK-L: WARNING: The program has no main() function.
// CHECK-L: WARNING: Possibly all assertions have been discharged by the front-end

// Based on https://github.com/MCFuzzer/MCFuzz/issues/44.

extern void __VERIFIER_error(void) __attribute__((noreturn));

void test(int x, int y, int q) {
  if ((x / y) != q)
    __VERIFIER_error();
}

int main() {
  test(7, 6, 1);
  test(-7, -6, 1);

  return 0;
}
