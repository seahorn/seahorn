#pragma once

#include "seahorn/Expr/Smt/Z3.hh"
#include "seahorn/Expr/Expr.hh"


namespace seahorn {
class ExprToZ {
public:
  /// \brief Convert Expr to z3::ast
  /// \p cache is a bidirectional map that is preserved across calls
  /// \p seen local map for current marshal call (in case it is recursive)
  template <typename C>
  static z3::ast marshal(expr::Expr e, z3::context &ctx, C &cache,
                         ufo::expr_ast_map &seen);
};
} // namespace seahorn
