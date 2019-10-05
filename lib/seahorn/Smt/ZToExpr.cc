#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Expr/Smt/ExprToZ.hh"
#include "seahorn/Expr/Smt/ZToExpr.def"

#include "seahorn/Expr/Smt/Z3.hh"

namespace seahorn {
template 
expr::Expr ZToExpr::unmarshal<typename ufo::EZ3::z_cache_type>(
    const z3::ast &, expr::ExprFactory &, typename ufo::EZ3::z_cache_type &,
    ufo::ast_expr_map &);
}
