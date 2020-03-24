/// Finite Maps
#pragma once
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/Expr.hh"

namespace expr {

namespace op {
enum class FiniteMapOpKind { CONST_FINITE_MAP, SET, GET };
/// FiniteMap operators
NOP_BASE(FiniteMapOp)

NOP(CONST_FINITE_MAP, "defk", FUNCTIONAL, FiniteMapOp)
NOP(GET, "get", FUNCTIONAL, FiniteMapOp)
NOP(SET, "set", FUNCTIONAL, FiniteMapOp)

} // namespace op

namespace op {
namespace finite_map {

inline Expr constFiniteMap(ExprVector keys) {
  return expr::mknary<CONST_FINITE_MAP>(keys.begin(), keys.end());
}

inline Expr get(Expr a, Expr idx) { return expr::mk<GET>(a, idx); }
// inline Expr get(Expr a, const ExprVector& keys, Expr idx) { return
// mk<GET>(a, keys, idx); }
inline Expr set(Expr a, Expr idx, Expr v) { return expr::mk<SET>(a, idx, v); }
// inline Expr set(Expr a, const ExprVector& keys, Expr idx, Expr v) { return
// mk<GET>(a, keys, idx, v); }

} // namespace finite_map
} // namespace op
}
