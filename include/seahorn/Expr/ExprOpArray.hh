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
    if (!checkNumChildren<Equal, 2>)
      return sort::errorTy(exp->efac());

    if (!correctType<ARRAY_TY>(exp->left(), tc))
      return sort::errorTy(exp->efac());

    Expr arrayType = tc.typeOf(exp->left());
    Expr indexTy = sort::arrayIndexTy(arrayType);
    Expr valTy = sort::arrayValTy(arrayType);

    if (indexTy == tc.typeOf(exp->right()))
      return valTy;
    else
      return sort::errorTy(exp->efac());
  }
};

struct Store {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (!checkNumChildren<Equal, 3>)
      return sort::errorTy(exp->efac());

    if (!correctType<ARRAY_TY>(exp->arg(0), tc))
      return sort::errorTy(exp->efac());

    Expr arrayType = tc.typeOf(exp->arg(0));
    Expr indexTy = sort::arrayIndexTy(arrayType);
    Expr valTy = sort::arrayValTy(arrayType);

    if (indexTy == tc.typeOf(exp->arg(1)) && valTy == tc.typeOf(exp->arg(2)))
      return arrayType;
    else
      return sort::errorTy(exp->efac());
  }
};

struct Const {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (!checkNumChildren<Equal, 2>)
      return sort::errorTy(exp->efac());

    Expr domain = exp->left();
    Expr value = exp->right();

    if (correctType<ANY_TY>(domain, tc) && correctType<ANY_TY>(value, tc))
      return sort::arrayTy(tc.typeOf(domain), tc.typeOf(value));
    else
      return sort::errorTy(exp->efac());
  }
};

struct Default {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (!checkNumChildren<Equal, 1>)
      return sort::errorTy(exp->efac());

    Expr array = exp->first();

    if (!correctType<ARRAY_TY>(array, tc))
      return sort::errorTy(exp->efac());

    return sort::arrayValTy(tc.typeOf(array));
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
