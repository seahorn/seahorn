#include "seahorn/Expr/Smt/ExprToZ.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Expr/Smt/ExprToZ.def"

#include "seahorn/Expr/Smt/Z3.hh"

namespace seahorn {
template z3::ast ExprToZ::marshal<typename EZ3::expr_cache_type>(
        const expr::Expr &, z3::context &, typename EZ3::expr_cache_type &,
        expr_ast_map &);
}
