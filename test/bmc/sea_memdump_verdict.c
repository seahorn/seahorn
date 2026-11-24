// sea_memdump outside the sea-mlir export: an external call that is passed
// its pointer; the verdict is the same with and without the calls (BMC, the
// default CHC flow, crab).
// RUN: %sea bpf -O3 --bmc=mono --bound=9 --inline "%s" 2>&1 | filecheck %s --check-prefix=UNSAT
// RUN: %sea bpf -O3 --bmc=mono --bound=9 --inline -DNO_DUMP "%s" 2>&1 | filecheck %s --check-prefix=UNSAT
// RUN: %sea bpf -O3 --bmc=mono --bound=9 --inline -DCEX "%s" 2>&1 | filecheck %s --check-prefix=SAT
// RUN: %sea bpf -O3 --bmc=mono --bound=9 --inline -DCEX -DNO_DUMP "%s" 2>&1 | filecheck %s --check-prefix=SAT
// RUN: %sea pf "%s" 2>&1 | filecheck %s --check-prefix=UNSAT
// RUN: %sea pf -DNO_DUMP "%s" 2>&1 | filecheck %s --check-prefix=UNSAT
// RUN: %sea pf -DCEX "%s" 2>&1 | filecheck %s --check-prefix=SAT
// RUN: %sea pf -DCEX -DNO_DUMP "%s" 2>&1 | filecheck %s --check-prefix=SAT
// RUN: %sea pf --crab "%s" 2>&1 | filecheck %s --check-prefix=UNSAT
// RUN: %sea pf --crab -DCEX "%s" 2>&1 | filecheck %s --check-prefix=SAT
// UNSAT: {{^unsat$}}
// SAT: {{^sat$}}

#include <seahorn/seahorn.h>
#include <stdint.h>

extern int nd_int(void);
struct S {
  uint32_t a;
  uint8_t b[6];
  uint16_t c;
};

#ifdef NO_DUMP
#define DUMP(l, p, n) ((void)0)
#else
#define DUMP(l, p, n) sea_memdump(l, p, n)
#endif

int main(void) {
  uint8_t buf[8];
  struct S s;
  for (int i = 0; i < 8; i++)
    buf[i] = (uint8_t)(nd_int() & 0x3f) + 'A';
  s.a = nd_int();
  s.b[0] = buf[0];
  s.c = 7;
  DUMP("buf", buf, sizeof buf);
  DUMP("s", &s, sizeof s);
  sassert(s.c == 7);
  sassert(buf[0] >= 'A');
#ifdef CEX
  sassert(buf[3] != 'Q' || s.a != 5);
#endif
  return 0;
}
