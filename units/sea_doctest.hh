// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

//
// Wrapper over doctest.h to workaround macro name clash with Sealog.hh
//

#ifndef SEAHORN_SEA_DOCTEST_HH
#define SEAHORN_SEA_DOCTEST_HH

// workaround(test): to avoid name clash with doctest.h
#undef WARN
#undef INFO
#include "doctest.h"
#endif // SEAHORN_SEA_DOCTEST_HH
