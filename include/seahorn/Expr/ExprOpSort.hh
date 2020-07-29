/// Sorts and types
#pragma once

#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/TypeCheckerBase.hh"
#include <string>

namespace expr {

namespace op {
enum class SimpleTypeOpKind {
  INT_TY,
  CHAR_TY,
  REAL_TY,
  VOID_TY,
  BOOL_TY,
  UNINT_TY,
  ARRAY_TY,
  STRUCT_TY,
  FINITE_MAP_TY,
  FINITE_MAP_KEYS_TY,
  ANY_TY,
  ERROR_TY,
  TYPE_TY,
  FUNCTIONAL_TY
};

namespace sort {

inline Expr typeTy(ExprFactory &efac);
}

namespace typeCheck {
namespace simpleType {
struct Simple : public TypeCheckBase{
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    return sort::typeTy(exp->efac());
  }
};
} // namespace simpleType
} // namespace typeCheck

NOP_BASE(SimpleTypeOp)

/// \brief Int type
NOP(INT_TY, "INT", PREFIX, SimpleTypeOp, typeCheck::simpleType::Simple)
/// \brief Char type (UNUSED)
NOP(CHAR_TY, "CHAR", PREFIX, SimpleTypeOp, typeCheck::simpleType::Simple)
/// \brief Real type
NOP(REAL_TY, "REAL", PREFIX, SimpleTypeOp, typeCheck::simpleType::Simple)
/// \brief Void type
NOP(VOID_TY, "VOID", PREFIX, SimpleTypeOp, typeCheck::simpleType::Simple)
/// \biref Boolean type
NOP(BOOL_TY, "BOOL", PREFIX, SimpleTypeOp, typeCheck::simpleType::Simple)
/// \brief Uninterpreted type
NOP(UNINT_TY, "UNINT", PREFIX, SimpleTypeOp, typeCheck::simpleType::Simple)
/// \brief Array type
NOP(ARRAY_TY, "ARRAY", PREFIX, SimpleTypeOp, typeCheck::simpleType::Simple)
/// \biref Struct type
NOP(STRUCT_TY, "STRUCT", PREFIX, SimpleTypeOp, typeCheck::simpleType::Simple)
/// \biref FiniteMap type
NOP(FINITE_MAP_TY, "FINITE_MAP", PREFIX, SimpleTypeOp, typeCheck::simpleType::Simple)
NOP(FINITE_MAP_KEYS_TY, "FINITE_MAP_KS", PREFIX, SimpleTypeOp, typeCheck::simpleType::Simple)
/// \brief ANY type
NOP(ANY_TY, "ANY", PREFIX, SimpleTypeOp, typeCheck::simpleType::Simple)
/// \brief Error type
NOP(ERROR_TY, "ERROR", PREFIX, SimpleTypeOp, typeCheck::simpleType::Simple)
/// \brief Type type,
NOP(TYPE_TY, "TYPE", PREFIX, SimpleTypeOp, typeCheck::Any)
/// \brief Functional type,
NOP(FUNCTIONAL_TY, "FUNCTIONAL", PREFIX, SimpleTypeOp,
    typeCheck::simpleType::Simple)
} // namespace op

namespace op {
namespace sort {
inline Expr intTy(ExprFactory &efac) { return mk<INT_TY>(efac); }
inline Expr boolTy(ExprFactory &efac) { return mk<BOOL_TY>(efac); }
inline Expr realTy(ExprFactory &efac) { return mk<REAL_TY>(efac); }
inline Expr unintTy(ExprFactory &efac) { return mk<UNINT_TY>(efac); }
inline Expr anyTy(ExprFactory &efac) { return mk<ANY_TY>(efac); }
inline Expr errorTy(ExprFactory &efac) { return mk<ERROR_TY>(efac); }
inline Expr typeTy(ExprFactory &efac) { return mk<TYPE_TY>(efac); }
inline Expr arrayTy(Expr indexTy, Expr valTy) {
  return mk<ARRAY_TY>(indexTy, valTy);
}
inline Expr arrayIndexTy(Expr a) { return a->left(); }
inline Expr arrayValTy(Expr a) { return a->right(); }

inline Expr structTy(Expr ty) { return mk<STRUCT_TY>(ty); }
inline Expr structTy(Expr ty1, Expr ty2) { return mk<STRUCT_TY>(ty1, ty2); }
inline Expr structTy(Expr ty1, Expr ty2, Expr ty3) {
  return mk<STRUCT_TY>(ty1, ty2, ty3);
}
template <typename Range> Expr structTy(const Range &ty) {
  return mknary<STRUCT_TY>(ty);
}

inline Expr finiteMapTy(Expr valTy, Expr k) { return mk<FINITE_MAP_TY>(valTy, mk<FINITE_MAP_KEYS_TY>(k));
}
inline Expr finiteMapTy(Expr valTy, Expr k1, Expr k2) {
  return mk<FINITE_MAP_TY>(valTy, mk<FINITE_MAP_KEYS_TY>(k1, k2));
}
template <typename Range>
Expr finiteMapTy(Expr valTy, const Range &ks) {
  // The keys already contain a type
  return mk<FINITE_MAP_TY>(valTy, mknary<FINITE_MAP_KEYS_TY>(ks));
}
inline Expr finiteMapKeyTy(Expr fmapTy) { return fmapTy->right(); }
inline Expr finiteMapValTy(Expr fmapTy) { return fmapTy->left(); }

} // namespace sort
} // namespace op
} // namespace expr
