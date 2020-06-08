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

template <unsigned NumChildren>
static inline bool checkArray(Expr exp, TypeChecker &tc) {
  return exp->arity() == NumChildren && isOp<ARRAY_TY>(tc.typeOf(exp->first()));
}

struct Select {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (!checkArray<2>(exp, tc))
      return sort::errorTy(exp->efac());

    Expr arrayTy = tc.typeOf(exp->left());
    Expr indexTy = sort::arrayIndexTy(arrayTy);
    Expr valTy = sort::arrayValTy(arrayTy);

    if (indexTy == tc.typeOf(exp->right()))
      return valTy;
    else
      return sort::errorTy(exp->efac());
  }
};
struct Store {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (!checkArray<3>(exp, tc))
      return sort::errorTy(exp->efac());

    Expr arrayTy = tc.typeOf(exp->left());
    Expr indexTy = sort::arrayIndexTy(arrayTy);
    Expr valTy = sort::arrayValTy(arrayTy);

    if (indexTy == tc.typeOf(exp->arg(1)) && valTy == tc.typeOf(exp->arg(2)))
      return arrayTy;
    else
      return sort::errorTy(exp->efac());
  }
};

struct Const {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (exp->arity() != 2)
      return sort::errorTy(exp->efac());

    Expr domain = exp->left();
    Expr value = exp->right();

    return sort::arrayTy(tc.typeOf(domain), tc.typeOf(value));
  }
};

struct Default {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {

    if (!checkArray<1>(exp, tc))
      return sort::errorTy(exp->efac());

    Expr array = exp->first();

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
