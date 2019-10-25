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

} // namespace path_bmc
} // namespace seahorn
