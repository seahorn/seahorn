#pragma once

#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/TypeChecker.hh"
#include "seahorn/Expr/TypeCheckerUtils.hh"

namespace expr {

namespace op {
enum class CompareOpKind { EQ, NEQ, LEQ, GEQ, LT, GT };
namespace typeCheck {
namespace compareType {

struct Equality {
  // Return type: BOOL_TY
  // Possible types of children: anything excepty for ERROR_TY
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::binary<BOOL_TY, ANY_TY>(exp, tc);
  }
};
struct Inequality {
  // Return type: BOOL_TY
  // Possible types of children: INT_TY, REAL_TY, UNINT_TY
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::binary<BOOL_TY, INT_TY, REAL_TY, UNINT_TY>(exp, tc);
  }
};
} // namespace compareType
} // namespace typeCheck

// -- Compare operators
NOP_BASE(CompareOp)

NOP_TYPECHECK(EQ, "=", INFIX, CompareOp, typeCheck::compareType::Equality)
NOP_TYPECHECK(NEQ, "!=", INFIX, CompareOp, typeCheck::compareType::Equality)
NOP_TYPECHECK(LEQ, "<=", INFIX, CompareOp, typeCheck::compareType::Inequality)
NOP_TYPECHECK(GEQ, ">=", INFIX, CompareOp, typeCheck::compareType::Inequality)
NOP_TYPECHECK(LT, "<", INFIX, CompareOp, typeCheck::compareType::Inequality)
NOP_TYPECHECK(GT, ">", INFIX, CompareOp, typeCheck::compareType::Inequality)
} // namespace op
} // namespace expr
