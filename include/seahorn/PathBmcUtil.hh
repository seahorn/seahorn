#pragma once

namespace seahorn {
namespace solver {
class Solver;
}
} // namespace seahorn

namespace seahorn {
namespace path_bmc {

struct scoped_solver {
  solver::Solver &m_solver;

public:
  /* Timeout in seconds*/
  scoped_solver(solver::Solver &solver, unsigned timeout);
  ~scoped_solver();
  solver::Solver &get() { return m_solver; }
};

} // namespace path_bmc
} // namespace seahorn
