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

static inline bool checkArray(Expr exp, TypeChecker &tc, unsigned numChildren) {
  return exp->arity() == numChildren &&
         correctTypeAny<ARRAY_TY>(exp->first(), tc);
}

struct Select {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (!checkArray(exp, tc, 2))
      return sort::errorTy(exp->efac());

    Expr arrayTy = tc.typeOf(exp->left());
    Expr indexTy = sort::arrayIndexTy(arrayTy);
    Expr valTy = sort::arrayValTy(arrayTy);

    if (indexTy == tc.typeOf(exp->right()))
      return valTy;

    return sort::errorTy(exp->efac());
  }
};
struct Store {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (!checkArray(exp, tc, 3))
      return sort::errorTy(exp->efac());

    Expr arrayTy = tc.typeOf(exp->left());
    Expr indexTy = sort::arrayIndexTy(arrayTy);
    Expr valTy = sort::arrayValTy(arrayTy);

    if (indexTy == tc.typeOf(exp->arg(1)) && valTy == tc.typeOf(exp->arg(2)))
      return arrayTy;

    return sort::errorTy(exp->efac());
  }
};

struct Const {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (exp->arity() != 2)
      return sort::errorTy(exp->efac());

    Expr domain = exp->left();
    Expr value = exp->right();

    if (isOp<TYPE_TY>(tc.typeOf(domain)))
      return sort::arrayTy(domain, tc.typeOf(value));

    return sort::errorTy(exp->efac());
  }
};

struct Default {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {

    if (!checkArray(exp, tc, 1))
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
NOP_TYPECHECK(ARRAY_MAP, "array-map", FUNCTIONAL, ArrayOp, typeCheck::Any)
NOP_TYPECHECK(ARRAY_DEFAULT, "array-default", FUNCTIONAL, ArrayOp,
              typeCheck::arrayType::Default)
NOP_TYPECHECK(AS_ARRAY, "as-array", FUNCTIONAL, ArrayOp, typeCheck::Any)
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
