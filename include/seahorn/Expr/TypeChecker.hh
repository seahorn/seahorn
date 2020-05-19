#pragma once

#include "seahorn/Expr/ExprApi.hh"

namespace expr {
class TypeChecker {
  class Impl;
  Impl *m_impl;

public:
  TypeChecker();
  ~TypeChecker();
  Expr sortOf(Expr e) { return this->typeOf(e); }
  Expr typeOf(Expr e);
  Expr getNotWellFormed(); // to be called of typeOf() or sortOf
};

} // namespace expr
