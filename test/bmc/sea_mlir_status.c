// The sea-mlir engine reports a verdict only for the sea-vc statuses that
// carry one (0, and 3 with `result: unknown`); any other status is no
// verdict whatever `result:` says. sea-vc is replaced by a script that prints
// `result: sat` and exits with the status under test.
// RUN: printf '#!/bin/sh\necho "result: sat"\nexit 0\n' > %t.0.sh
// RUN: printf '#!/bin/sh\necho "result: sat"\nexit 2\n' > %t.2.sh
// RUN: printf '#!/bin/sh\necho "result: sat"\nexit 3\n' > %t.3.sh
// RUN: printf '#!/bin/sh\necho "result: sat"\nexit 4\n' > %t.4.sh
// RUN: chmod +x %t.0.sh %t.2.sh %t.3.sh %t.4.sh
// RUN: %sea bpf -O0 --bmc=mono --horn-bmc-engine=sea-mlir --horn-sea-vc=%t.0.sh "%s" 2>&1 | filecheck %s --check-prefix=OK
// RUN: %sea bpf -O0 --bmc=mono --horn-bmc-engine=sea-mlir --horn-sea-vc=%t.2.sh "%s" 2>&1 | filecheck %s --check-prefix=NO
// RUN: %sea bpf -O0 --bmc=mono --horn-bmc-engine=sea-mlir --horn-sea-vc=%t.3.sh "%s" 2>&1 | filecheck %s --check-prefix=NO
// RUN: %sea bpf -O0 --bmc=mono --horn-bmc-engine=sea-mlir --horn-sea-vc=%t.4.sh "%s" 2>&1 | filecheck %s --check-prefix=NO
// OK: {{^}}sat{{$}}
// NO: {{^}}unknown{{$}}

extern int nd(void);
extern void __VERIFIER_error(void);
int main(void) {
  int x = nd();
  if (x == 3)
    __VERIFIER_error();
  return 0;
}
