#pragma once

#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"

namespace expr {

namespace op {
enum class CompareOpKind { EQ, NEQ, LEQ, GEQ, LT, GT };
// -- Compare operators
NOP_BASE(CompareOp)

NOP(EQ, "=", INFIX, CompareOp)
NOP(NEQ, "!=", INFIX, CompareOp)
NOP(LEQ, "<=", INFIX, CompareOp)
NOP(GEQ, ">=", INFIX, CompareOp)
NOP(LT, "<", INFIX, CompareOp)
NOP(GT, ">", INFIX, CompareOp)
} // namespace op
}
