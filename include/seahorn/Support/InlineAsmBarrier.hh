// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#pragma once
/// Inline assembly that is only a compiler barrier, shared by BvOpSem2 and
/// the sea-mlir export so that both back ends accept the same asm.

#include "llvm/ADT/StringRef.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstrTypes.h"

namespace seahorn {

/// True if \p CB calls inline assembly \p IA that has no effect on values:
/// - its body is empty or only assembler comments (every line, after
///   whitespace, empty or starting with '#'; Firedancer's
///   FD_COMPILER_MFENCE is `"# FD_COMPILER_MFENCE()@file(line)"`);
/// - it returns nothing and its operands are only register inputs ("r",
///   used to keep a value alive);
/// - it clobbers only memory and the flags: ~{memory}, ~{cc},
///   ~{dirflag}, ~{fpsr}, ~{flags}.
inline bool isInlineAsmBarrier(const llvm::CallBase &CB,
                               const llvm::InlineAsm &IA) {
  if (!CB.getType()->isVoidTy())
    return false;
  llvm::StringRef body = IA.getAsmString();
  while (!body.empty()) {
    auto [line, rest] = body.split('\n');
    line = line.trim();
    if (!line.empty() && !line.starts_with("#"))
      return false;
    body = rest;
  }
  for (const llvm::InlineAsm::ConstraintInfo &ci : IA.ParseConstraints()) {
    if (ci.Codes.size() != 1)
      return false;
    llvm::StringRef code = ci.Codes[0];
    switch (ci.Type) {
    case llvm::InlineAsm::isInput:
      if (ci.isIndirect || code != "r")
        return false;
      break;
    case llvm::InlineAsm::isClobber:
      if (code != "{memory}" && code != "{cc}" && code != "{dirflag}" &&
          code != "{fpsr}" && code != "{flags}")
        return false;
      break;
    default:
      return false;
    }
  }
  return true;
}

} // namespace seahorn
