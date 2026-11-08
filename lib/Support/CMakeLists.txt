# SPDX-FileCopyrightText: 2026 The SeaHorn Authors
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

add_llvm_library (SeaSupport DISABLE_LLVM_LINK_LLVM_DYLIB
  SortTopo.cc
  Stats.cc
  Profiler.cc
  CFGPrinter.cc
  SeaLog.cc
  SeaDebug.cc
  GitSHA1.cc
  BoostException.cc
  )
