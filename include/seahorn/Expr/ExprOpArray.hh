/// Arrays
#pragma once
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"

namespace expr {

namespace op {
enum class ArrayOpKind {
  SELECT,
  STORE,
  CONST_ARRAY,
  ARRAY_MAP,
  ARRAY_DEFAULT,
  AS_ARRAY
};

namespace typeCheck {
namespace arrayType {
struct Select {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    auto returnTypeFn = [](Expr exp, TypeChecker &tc) {
      Expr arrayTy = tc.typeOf(exp->left());
      Expr indexTy = sort::arrayIndexTy(arrayTy);
      Expr valTy = sort::arrayValTy(arrayTy);

      if (indexTy == tc.typeOf(exp->right()))
        return valTy;
      else
        return sort::errorTy(exp->efac());
    };
    return typeCheck::checkChildrenSpecific<Equal, 2, ARRAY_TY, ANY_TY>(
        exp, tc, returnTypeFn);
  }
};

struct Store {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    auto returnTypeFn = [](Expr exp, TypeChecker &tc) {
      Expr arrayTy = tc.typeOf(exp->arg(0));
      Expr indexTy = sort::arrayIndexTy(arrayTy);
      Expr valTy = sort::arrayValTy(arrayTy);

      if (indexTy == tc.typeOf(exp->arg(1)) && valTy == tc.typeOf(exp->arg(2)))
        return arrayTy;
      else
        return sort::errorTy(exp->efac());
    };
    return typeCheck::checkChildrenSpecific<Equal, 3, ARRAY_TY, ANY_TY, ANY_TY>(
        exp, tc, returnTypeFn);
  }
};

struct Const {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    auto returnTypeFn = [](Expr exp, TypeChecker &tc) {
      Expr domain = exp->left();
      Expr value = exp->right();

      return sort::arrayTy(tc.typeOf(domain), tc.typeOf(value));
    };

    return typeCheck::checkChildrenSpecific<Equal, 2, ANY_TY, ANY_TY>(
        exp, tc, returnTypeFn);
  }
};

struct Default {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    auto returnTypeFn = [](Expr exp, TypeChecker &tc) {
      Expr array = exp->first();

      return sort::arrayValTy(tc.typeOf(array));
    };
    return typeCheck::checkChildrenSpecific<Equal, 1, ARRAY_TY>(exp, tc,
                                                                returnTypeFn);
  }
};
} // namespace arrayType
} // namespace typeCheck

/// Array operators
NOP_BASE(ArrayOp)

NOP_TYPECHECK(SELECT, "select", FUNCTIONAL, ArrayOp,
              typeCheck::arrayType::Select)
NOP_TYPECHECK(STORE, "store", FUNCTIONAL, ArrayOp, typeCheck::arrayType::Store)
NOP_TYPECHECK(CONST_ARRAY, "const-array", FUNCTIONAL, ArrayOp,
              typeCheck::arrayType::Const)
NOP(ARRAY_MAP, "array-map", FUNCTIONAL, ArrayOp)
NOP_TYPECHECK(ARRAY_DEFAULT, "array-default", FUNCTIONAL, ArrayOp,
              typeCheck::arrayType::Default)
NOP(AS_ARRAY, "as-array", FUNCTIONAL, ArrayOp)
} // namespace op

namespace op {
namespace array {
inline Expr select(Expr a, Expr idx) { return mk<SELECT>(a, idx); }
inline Expr store(Expr a, Expr idx, Expr v) { return mk<STORE>(a, idx, v); }
inline Expr constArray(Expr domain, Expr v) {
  return mk<CONST_ARRAY>(domain, v);
}
inline Expr aDefault(Expr a) { return mk<ARRAY_DEFAULT>(a); }
} // namespace array
} // namespace op
} // namespace expr
