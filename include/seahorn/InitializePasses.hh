// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#pragma once
#include "llvm/InitializePasses.h"
#include "llvm/PassRegistry.h"
namespace llvm {
void initializeSimpleMemoryCheckPass(PassRegistry &);
void initializeFatBufferBoundsCheckPass(PassRegistry &);
void initializeSeaBuiltinsInfoWrapperPassPass(PassRegistry &);
void initializeGeneratePartialFnPassPass(PassRegistry &);
void initializeLoopPeelerPassPass(PassRegistry &);
void initializeAddBranchSentinelPassPass(PassRegistry &);
void initializeEvalBranchSentinelPassPass(PassRegistry &);
}
