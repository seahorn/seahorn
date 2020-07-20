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
  static inline Expr inferType(Expr exp, TypeChecker &tc) {

    // finite maps are a special case: the keys are stored directly, not as
    // their type
    if (isOp<FINITE_MAP_TY>(tc.typeOf(exp->first()))) {
      if (!(exp->arity() == 2 && isOp<FINITE_MAP_TY>(tc.typeOf(exp->right()))))
        return sort::errorTy(exp->efac());

      Expr leftType = tc.typeOf(exp->left());
      Expr rightType = tc.typeOf(exp->right());

      bool sameValTy =
          sort::finiteMapValTy(leftType) == sort::finiteMapValTy(rightType);
      bool sameNumKeys = sort::finiteMapKeyTy(leftType)->arity() ==
                         sort::finiteMapKeyTy(rightType)->arity();
      bool sameKeyTy =
          tc.typeOf(sort::finiteMapKeyTy(leftType)->first()) ==
          tc.typeOf(sort::finiteMapKeyTy(leftType)
                        ->first()); // just check that the keys have the same
                                    // type, not necessarily the same name

      if (sameValTy && sameNumKeys && sameKeyTy) {
        return sort::boolTy(exp->efac());
      }

      return sort::errorTy(exp->efac());
    }

    return typeCheck::binary<BOOL_TY, ANY_TY>(exp, tc);
  }
};
struct Inequality {
  /// \return BOOL_TY
  /// Possible types of children: any number type
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::binary<BOOL_TY, NUM_TYPES>(exp, tc);
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
