
#pragma once

#include "seahorn/Expr/TypeChecker.hh"

namespace expr {
namespace op {
namespace typeCheck {

struct TypeCheckBase {

  /// \return true to infer the type of the current expression before visiting
  /// its children
  virtual inline bool topDown() { return false; };

  /// \return the type of the expression
  virtual inline Expr inferType(Expr exp, TypeChecker &tc) = 0;
};
} // namespace typeCheck
} // namespace op
} // namespace expr
