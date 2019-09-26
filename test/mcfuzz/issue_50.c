// RUN: %sea bpf -m32 -O0 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m32 -O3 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s --check-prefix=OLD
// RUN: %sea bpf -m64 -O3 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s --check-prefix=OLD

// CHECK-L: unsat
// OLD-L: sat

// Based on https://github.com/MCFuzzer/MCFuzz/issues/52.
// With the old bv-opsem we get sat.

extern void __VERIFIER_error(void) __attribute__((noreturn));

int _br_1 = 0;

char *p = "abc\n";
;

static int is_end_of_statement(void) { return *p == '\n'; }

void foo(void) {
  while (!is_end_of_statement()) {
    _br_1++;
    p++;
  }
}

int main(void) {
  foo();
  if (_br_1 != 3)
    __VERIFIER_error();
  return 0;
}
