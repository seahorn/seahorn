// RUN: %sea bpf -m32 -O0 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m32 -O3 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats --log=opsem "%s" 2>&1 | OutputCheck %s

// CHECK-L: unsat
// XFAIL: *

// Based on https://github.com/MCFuzzer/MCFuzz/issues/49.
// We crash in MixedSemantics.

extern void __VERIFIER_error(void) __attribute__((noreturn));

void bar(int *pc) {
  static const void *l[] = {&&lab0, &&end};
  goto *l[*pc];
lab0:
  pc++;
  goto *l[*pc];
end : { __VERIFIER_error(); }
  return;
}

int main() {
  bar(0);
  return 0;
}