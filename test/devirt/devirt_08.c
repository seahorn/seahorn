// Under LLVM-15 opaque pointers sea-dsa does not resolve a function
// pointer stored in a struct field and reached via a returned struct pointer,
// so the call stays indirect and BMC reports sat.
// Blocked on sea-dsa bug: https://github.com/seahorn/sea-dsa/issues/176
// XFAIL: *
// RUN: %sea pf -O0 --devirt-functions=sea-dsa --devirt-functions-allow-indirect-calls "%s"  2>&1 | filecheck %s
// CHECK: {{^unsat$}}

#include "seahorn/seahorn.h"

typedef int (*handler_t)();

struct test_handler{
    handler_t handler;
};

int foo() {
    int i = 0;
    sassert(i == 0);
    return i;
}

struct test_handler handler_var = {
    .handler = foo
};

struct test_handler *return_handler_struct() {
    return &handler_var;
}

int main(int argc, char** argv) {
    struct test_handler *res = return_handler_struct();
    sassert(res->handler() == 0);
    return 0;
}
