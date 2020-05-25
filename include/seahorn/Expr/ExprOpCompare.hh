#pragma once

#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/TypeChecker.hh"

namespace expr {

namespace op {
enum class CompareOpKind { EQ, NEQ, LEQ, GEQ, LT, GT };
namespace typeCheck {
namespace compareType {

    // ensures: 1. correct number of children, 2. both children are the same type
    static inline bool checkChildren (Expr exp, TypeChecker &tc) {
        return exp->arity() == 2 && (tc.typeOf(exp->arg(0)) == tc.typeOf(exp->arg(1)));
    }
   struct Equality {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (checkChildren(exp, tc))
      return sort::boolTy(exp->efac());
    else
      return sort::errorTy(exp->efac());
  }
};
struct Inequality {
    static inline bool isNumType (Expr exp) {
        if (isOp<INT_TY>(exp) || isOp<REAL_TY>(exp) || isOp<UNINT_TY>(exp)) 
            return true;
        return false;
    }
  static inline Expr inferType(Expr exp, TypeChecker &tc) {

    if (checkChildren(exp, tc) && isNumType(tc.typeOf(exp->first())))
      return sort::boolTy(exp->efac());
    else
      return sort::errorTy(exp->efac());
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
