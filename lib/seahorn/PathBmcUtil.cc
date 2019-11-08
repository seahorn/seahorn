#include "seahorn/PathBmcUtil.hh"

#include "seahorn/Expr/Smt/Solver.hh"
#ifdef WITH_YICES2
#include "seahorn/Expr/Smt/Yices2SolverImpl.hh"
#endif
#include "seahorn/Expr/Smt/Z3SolverImpl.hh"

namespace seahorn {
namespace path_bmc {

scoped_solver::scoped_solver(solver::Solver &solver, unsigned timeout /*sec*/)
    : m_solver(solver) {
  if (m_solver.get_kind() == solver::SolverKind::Z3) {
    solver::z3_solver_impl &z3 =
        static_cast<solver::z3_solver_impl &>(m_solver);
    ZParams<EZ3> params(z3.get_context());
    // We should check here for possible overflow if timeout is
    // given, e.g., in miliseconds.
    params.set(":timeout", timeout * 1000);
    z3.get_solver().set(params);
  } else {
#ifdef WITH_YICES2
    // TODOX: add timeout capabilities to Yices2
#endif
  }
}

scoped_solver::~scoped_solver() {
  if (m_solver.get_kind() == solver::SolverKind::Z3) {
    solver::z3_solver_impl &z3 =
        static_cast<solver::z3_solver_impl &>(m_solver);
    ZParams<EZ3> params(z3.get_context());
    params.set(":timeout", 4294967295u); // disable timeout
    z3.get_solver().set(params);
  }
}


namespace expr_utils {
bool isEdge(Expr e) {
  return expr::op::bind::isFdecl(e->left()) &&
    isOpX<TUPLE>(e->left()->left());
}

std::pair<Expr, Expr> getEdge(Expr e) {
  assert(isEdge(e));
  Expr tuple = e->left()->left();
  Expr src = tuple->left();
  Expr dst = tuple->right();
  return std::make_pair(src, dst);
}

expr::Expr mkEdge(expr::Expr e1, expr::Expr e2) {
  return bind::boolConst(mk<TUPLE>(e1, e2)); 
}

// /*
//  * Customized ordering to ensure that non-tuple expressions come
//  * first than tuple expressions, otherwise standard ordering between
//  * Expr's.
//  */
// struct lessExpr {
//   bool operator()(Expr e1, Expr e2) const {
//     if (!isEdge(e1) && isEdge(e2))
//       return true;
//     else if (isEdge(e1) && !isEdge(e2))
//       return false;
//     else
//       return e1 < e2;
//   }
// };

} // namespace expr_utils
} // namespace path_bmc
} // namespace seahorn
