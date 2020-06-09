#pragma once
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpSort.hh"

namespace expr {
class TypeChecker {
  class Impl;
  Impl *m_impl;

public:
  TypeChecker();
  ~TypeChecker();
  Expr sortOf(Expr e) { return this->typeOf(e); }
  Expr typeOf(Expr e);
  Expr getErrorExp();         // to be called after typeOf() or sortOf()
  ExprSet getEndExps(Expr e); // to be called after typeOf() or sortOf()
};
} // namespace expr
