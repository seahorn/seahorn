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
  /// \return BOOL_TY
  /// Possible types of children: any type except for ERROR_TY
  static inline Expr inferType(Expr exp, TypeCheckerHelper &helper) {
    return typeCheck::binary<BOOL_TY, ANY_TY>(exp, helper);
  }
};
struct Inequality {
  /// \return BOOL_TY
  /// Possible types of children: any number type 
  static inline Expr inferType(Expr exp, TypeCheckerHelper &helper) {
    return typeCheck::binary<BOOL_TY, NUM_TYPES>(exp, helper);
  }
};
} // namespace compareType
} // namespace typeCheck

// -- Compare operators
NOP_BASE(CompareOp)

NOP(EQ, "=", INFIX, CompareOp, typeCheck::compareType::Equality)
NOP(NEQ, "!=", INFIX, CompareOp, typeCheck::compareType::Equality)
NOP(LEQ, "<=", INFIX, CompareOp, typeCheck::compareType::Inequality)
NOP(GEQ, ">=", INFIX, CompareOp, typeCheck::compareType::Inequality)
NOP(LT, "<", INFIX, CompareOp, typeCheck::compareType::Inequality)
NOP(GT, ">", INFIX, CompareOp, typeCheck::compareType::Inequality)
} // namespace op
} // namespace expr
