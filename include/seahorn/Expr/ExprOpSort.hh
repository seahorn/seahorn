/// Sorts and types
#pragma once

#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"

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
  STRUCT_TY
};
NOP_BASE(SimpleTypeOp)

/// \brief Int type
NOP(INT_TY, "INT", PREFIX, SimpleTypeOp)
/// \brief Char type (UNUSED)
NOP(CHAR_TY, "CHAR", PREFIX, SimpleTypeOp)
/// \brief Real type
NOP(REAL_TY, "REAL", PREFIX, SimpleTypeOp)
/// \brief Void type
NOP(VOID_TY, "VOID", PREFIX, SimpleTypeOp)
/// \biref Boolean type
NOP(BOOL_TY, "BOOL", PREFIX, SimpleTypeOp)
/// \brief Uninterpreted type
NOP(UNINT_TY, "UNINT", PREFIX, SimpleTypeOp)
/// \brief Array type
NOP(ARRAY_TY, "ARRAY", PREFIX, SimpleTypeOp)
/// \biref Struct type
NOP(STRUCT_TY, "STRUCT", PREFIX, SimpleTypeOp)
} // namespace op

namespace op {
namespace sort {
inline Expr intTy(ExprFactory &efac) { return mk<INT_TY>(efac); }
inline Expr boolTy(ExprFactory &efac) { return mk<BOOL_TY>(efac); }
inline Expr realTy(ExprFactory &efac) { return mk<REAL_TY>(efac); }
inline Expr arrayTy(Expr indexTy, Expr valTy) {
  return mk<ARRAY_TY>(indexTy, valTy);
}
inline Expr arrayIndexTy(Expr a) { return a->left(); }
inline Expr arrayValTy(Expr a) { return a->right(); }

inline Expr structTy(Expr ty) { return mk<STRUCT_TY>(ty); }
inline Expr structTy(Expr ty1, Expr ty2) { return mk<STRUCT_TY>(ty1, ty2); }
template <typename Range> Expr structTy(const Range &ty) {
  return mknary<STRUCT_TY>(ty);
}

} // namespace sort
} // namespace op
}
