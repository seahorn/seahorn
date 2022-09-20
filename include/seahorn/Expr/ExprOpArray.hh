/// Arrays
#pragma once
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/TypeCheckerMapUtils.hh"

namespace expr {

namespace op {
enum class ArrayOpKind {
  SELECT,
  STORE,
  CONST_ARRAY,
  ARRAY_MAP,
  ARRAY_DEFAULT,
  AS_ARRAY,
  STORE_MAP
};

namespace typeCheck {
namespace arrayType {

static inline bool checkArray(Expr exp, TypeChecker &tc, unsigned numChildren) {
  return exp->arity() == numChildren &&
         correctTypeAny<ARRAY_TY>(exp->first(), tc);
}

static inline void getArrayTypes(Expr exp, TypeChecker &tc, Expr &mapTy, Expr &indexTy, Expr &valTy) {
  mapTy = tc.typeOf(exp->left());
  indexTy = sort::arrayIndexTy(mapTy);
  valTy = sort::arrayValTy(mapTy);
}

  ///ensures that the expression's key type matches the arrays's key type
  /// checks for the following children (in order): map, index
  /// \return the array's value type
struct Select  : public TypeCheckBase{
  inline Expr inferType(Expr exp, TypeChecker &tc) override {
    return typeCheck::mapType::select<ARRAY_TY>(exp, tc, getArrayTypes);
  }
};

  /// ensures that the index type and value type match the array's index and value types
  /// checks for the following children (in order): array, index, value
  /// \return ARRAY_TY
struct Store  : public TypeCheckBase{
  inline Expr inferType(Expr exp, TypeChecker &tc) override {
    return typeCheck::mapType::store<ARRAY_TY>(exp, tc, getArrayTypes);
  }
};

  /// Expected Children types(in order): TYPE_TY, anything
  /// \return: ARRAY_TY
struct Const  : public TypeCheckBase{
  inline Expr inferType(Expr exp, TypeChecker &tc) override {
    if (exp->arity() != 2)
      return sort::errorTy(exp->efac());

    Expr domain = exp->left();
    Expr value = exp->right();

    if (isOp<TYPE_TY>(tc.typeOf(domain)))
      return sort::arrayTy(domain, tc.typeOf(value));

    return sort::errorTy(exp->efac());
  }
};

  /// Expected Children type: ARRAY_TY
  /// \return: ARRAY_TY
struct Default  : public TypeCheckBase{
  inline Expr inferType(Expr exp, TypeChecker &tc) override {

    if (!checkArray(exp, tc, 1))
      return sort::errorTy(exp->efac());

    Expr array = exp->first();

    return sort::arrayValTy(tc.typeOf(array));
  }
};

struct StoreMap : public TypeCheckBase {
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    /* store-map(array, base, list of structs) */
    return typeCheck::mapType::store_map<ARRAY_TY>(exp, tc, getArrayTypes);
  }
};
} // namespace arrayType
} // namespace typeCheck

/// Array operators
NOP_BASE(ArrayOp)

NOP(SELECT, "select", FUNCTIONAL, ArrayOp,
              typeCheck::arrayType::Select)
NOP(STORE, "store", FUNCTIONAL, ArrayOp, typeCheck::arrayType::Store)
NOP(CONST_ARRAY, "const-array", FUNCTIONAL, ArrayOp,
              typeCheck::arrayType::Const)
NOP(ARRAY_MAP, "array-map", FUNCTIONAL, ArrayOp, typeCheck::Any)
NOP(ARRAY_DEFAULT, "array-default", FUNCTIONAL, ArrayOp,
              typeCheck::arrayType::Default)
NOP(AS_ARRAY, "as-array", FUNCTIONAL, ArrayOp, typeCheck::Any)
NOP(STORE_MAP, "store-map", FUNCTIONAL, ArrayOp, typeCheck::arrayType::StoreMap)
} // namespace op

namespace op {
namespace array {
inline Expr select(Expr a, Expr idx) { return mk<SELECT>(a, idx); }
inline Expr selectArray(Expr sel) {
  assert(isOpX<SELECT>(sel));
  return sel->arg(0);
}
inline Expr selectIdx(Expr sel) {
  assert(isOpX<SELECT>(sel));
  return sel->arg(1);
}
inline Expr store(Expr a, Expr idx, Expr v) { return mk<STORE>(a, idx, v); }

bool ovCmp(const Expr a, const Expr b);

/* Container should be nary node type, usually struct */
template <typename R, typename Container>
inline Expr storeMap(Expr a, Expr base, R &map) {
  std::sort(map.begin(), map.end(), ovCmp); // usually only 2 elements
  return mk<STORE_MAP>(a, base, mknary<Container>(map));
}

/** @brief get offset-value map of storeMap **/
inline Expr storeMapGetMap(Expr stm) {
  assert(isOpX<STORE_MAP>(stm));
  return stm->arg(2);
}

Expr storeMapInsert(Expr stm, Expr ov);

Expr storeMapFind(Expr stm, Expr o);

inline Expr storeArray(Expr st) {
  assert(isOpX<STORE>(st));
  return st->arg(0);
}
inline Expr storeIdx(Expr st) {
  assert(isOpX<STORE>(st));
  return st->arg(1);
}
inline Expr storeVal(Expr st) {
  assert(isOpX<STORE>(st));
  return st->arg(2);
}
inline Expr constArray(Expr domain, Expr v) {
  return mk<CONST_ARRAY>(domain, v);
}
inline Expr aDefault(Expr a) { return mk<ARRAY_DEFAULT>(a); }
} // namespace array
} // namespace op
} // namespace expr
