#pragma once

#include "seahorn/Expr/Expr.hh"

namespace seahorn {
namespace solver {
class Solver;
}
} // namespace seahorn

namespace seahorn {
namespace path_bmc {

struct scopedSolver {
  solver::Solver &m_solver;

public:
  /* Timeout in seconds*/
  scopedSolver(solver::Solver &solver, unsigned timeout);
  ~scopedSolver();
  solver::Solver &get() { return m_solver; }
};
} // namespace path_bmc
} // namespace seahorn

namespace seahorn {
namespace path_bmc {
namespace expr_utils {
/* Return true if e is an edge between blocks in the encoding */
bool isEdge(expr::Expr e);
/* Return the edge elements as a pair */
std::pair<expr::Expr, expr::Expr> getEdge(expr::Expr e);
/* Make an edge */
expr::Expr mkEdge(expr::Expr e1, expr::Expr e2);
} // namespace expr_utils
} // namespace path_bmc
} // namespace seahorn
