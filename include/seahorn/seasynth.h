// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#pragma once

#ifdef sassert
#error Partial function synthesis requires that only seahorn/seasynth.h is included.
#elif defined(VACCHECK)
#error Partial function synthesis does not support vacuity checking.
#endif

#define SEA_SYNTH
#include "seahorn/seahorn.h"
