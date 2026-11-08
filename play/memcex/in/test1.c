// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include "memcex.h"

// reading non-deterministic pointer

int main(void) {
    if (__VERIFIER_nondet_ptr() > 0) {
        __VERIFIER_error();
    }
    return 0;
}
