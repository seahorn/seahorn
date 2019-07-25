// RUN: %sea bpf -m64 -O0 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O0 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s

// CHECK-L: unsat
// XFAIL: *

// Based on https://github.com/MCFuzzer/MCFuzz/issues/50.
// The old bv-opsem gives sat.

extern void __VERIFIER_error(void) __attribute__((noreturn));

int _br_1 = 0;
void test(const char *in) {
  while (1) {
    if (*in == 'a') {
      _br_1++;
      const char *p = in + 1;
      if (*p == 'b') {
        _br_1++;
        return;
      }
      in++;
    }
  }
}

void _stub() {
  if (!((_br_1 == 2)))
    __VERIFIER_error();
}

int main() {
  test("aab");
  _stub();
  return 0;
}
