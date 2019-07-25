// RUN: %sea bpf -m64 -O0 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --horn-bv2=true --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s

// RUN: %sea bpf -m64 -O0 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -m64 -O3 --bmc=mono --inline --bound=8 --keep-shadows=true --horn-stats "%s" 2>&1 | OutputCheck %s

// CHECK-L: WARNING: The program has no main() function.
// CHECK-L: WARNING: Possibly all assertions have been discharged by the front-end

// Based on https://github.com/MCFuzzer/MCFuzz/issues/51.

extern void __VERIFIER_error(void) __attribute__((noreturn));

struct S {
  unsigned char b, g, r, a;
};

union U {
  struct S c;
  unsigned v;
};

unsigned bar() {
  union U z;
  z.c.a = 255;
  return z.v;
}

int main() {
  union U c;
  c.v = bar();
  if (c.c.a != 255) {
    __VERIFIER_error();
  }
  return 0;
}
