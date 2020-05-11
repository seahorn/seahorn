
/// Sorts and types
#pragma once

#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/ExprOpSort.hh"
#include <string>
namespace expr {

namespace op {

enum class TerminalTypeOpKind {
  STRING_TERMINAL_TY,
  UINT_TERMINAL_TY,
  MPQ_TERMINAL_TY,
  MPZ_TERMINAL_TY,
  BVAR_TERMINAL_TY,
  LLVM_VALUE_TERMINAL_TY,
  LLVM_BASICBLOCK_TERMINAL_TY,
  LLVM_FUNCTION_TERMINAL_TY
};

NOP_BASE(TerminalTypeOp)

/// \brief String terminal type,
NOP(STRING_TERMINAL_TY, "STRING TERMINAL", PREFIX, TerminalTypeOp, typeCheck::simpleType::Simple)
/// \brief Uint terminal type,
NOP(UINT_TERMINAL_TY, "UINT TERMINAL", PREFIX, TerminalTypeOp, typeCheck::simpleType::Simple)
/// \brief GMP rational terminal type,
NOP(MPQ_TERMINAL_TY, "MPQ TERMINAL", PREFIX, TerminalTypeOp, typeCheck::simpleType::Simple)
/// \brief GMP integer terminal type,
NOP(MPZ_TERMINAL_TY, "MPZ TERMINAL", PREFIX, TerminalTypeOp, typeCheck::simpleType::Simple)
/// \brief Bounded variable terminal type,
NOP(BVAR_TERMINAL_TY, "BVAR TERMINAL", PREFIX, TerminalTypeOp, typeCheck::simpleType::Simple)
/// \brief llvm::Value terminal type,
NOP(LLVM_VALUE_TERMINAL_TY, "LLVM::VALUE TERMINAL", PREFIX, TerminalTypeOp, typeCheck::simpleType::Simple)
/// \brief llvm::BasicBlock terminal type,
NOP(LLVM_BASICBLOCK_TERMINAL_TY, "LLVM::BASICBLOCK TERMINAL", PREFIX, TerminalTypeOp, typeCheck::simpleType::Simple)
/// \brief llvm::Function terminal type,
NOP(LLVM_FUNCTION_TERMINAL_TY, "LLVM::FUNCTION TERMINAL", PREFIX, TerminalTypeOp, typeCheck::simpleType::Simple)
} // namespace op

namespace op {
namespace sort {
inline Expr stringTerminalTy(ExprFactory &efac) { return mk<STRING_TERMINAL_TY>(efac); }
inline Expr uintTerminalTy(ExprFactory &efac) { return mk<UINT_TERMINAL_TY>(efac); }
inline Expr mpqTerminalTy(ExprFactory &efac) { return mk<MPQ_TERMINAL_TY>(efac); }
inline Expr mpzTerminalTy(ExprFactory &efac) { return mk<MPZ_TERMINAL_TY>(efac); }
inline Expr bvarTerminalTy(ExprFactory &efac) { return mk<BVAR_TERMINAL_TY>(efac); }
inline Expr llvmValueTerminalTy(ExprFactory &efac) { return mk<LLVM_VALUE_TERMINAL_TY>(efac); }
inline Expr llvmBasicBlockTerminalTy(ExprFactory &efac) { return mk<LLVM_BASICBLOCK_TERMINAL_TY>(efac); }
inline Expr llvmFunctionTerminalTy(ExprFactory &efac) { return mk<LLVM_FUNCTION_TERMINAL_TY>(efac); }

} // namespace sort
} // namespace op
} // namespace expr
