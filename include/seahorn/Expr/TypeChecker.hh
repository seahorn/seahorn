#pragma once
#include "seahorn/Expr/ExprCore.hh"

namespace expr {
class TypeChecker {
  class Impl;
  Impl *m_impl;

public:
  TypeChecker();
  ~TypeChecker();
  Expr sortOf(Expr e) { return this->typeOf(e); }
  Expr typeOf(Expr e);
  Expr getErrorExp(); // to be called after typeOf() or sortOf()
};

namespace op {
namespace typeCheck {
struct ANY {
  static inline Expr inferType(Expr exp, TypeChecker &tc);
};
} // namespace typeCheck
} // namespace op
} // namespace expr
