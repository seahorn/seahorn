#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/Smt/Solver.hh"

namespace seahorn {
namespace path_bmc {

enum class MucMethodKind {
  MUC_NONE,
  MUC_DELETION,
  MUC_ASSUMPTIONS,
  MUC_BINARY_SEARCH
};

/** General API to compute unsat cores **/
class minimal_unsat_core {
protected:
  solver::Solver &m_solver;

public:
  minimal_unsat_core(solver::Solver &solver) : m_solver(solver) {}

  virtual void run(const expr::ExprVector &f, expr::ExprVector &core) = 0;

  virtual std::string get_name(void) const = 0;
};

class muc_with_assumptions : public minimal_unsat_core {

  void unsat_core(const expr::ExprVector &f, bool simplify,
                  expr::ExprVector &out);

public:
  muc_with_assumptions(solver::Solver &solver);

  void run(const expr::ExprVector &f, expr::ExprVector &core) override;

  std::string get_name(void) const override { return "MUC with assumptions"; }
};

class binary_search_muc;

class deletion_muc : public minimal_unsat_core {

  friend class binary_search_muc;

  typedef expr::ExprVector::const_iterator const_iterator;

  solver::SolverResult check(const_iterator it, const_iterator et,
                             const expr::ExprVector &assumptions);

  void run(const expr::ExprVector &f, const expr::ExprVector &assumptions,
           expr::ExprVector &out);

  unsigned m_timeout; /*seconds*/

public:
  deletion_muc(solver::Solver &solver, unsigned timeout);

  void run(const expr::ExprVector &f, expr::ExprVector &out) override;

  std::string get_name() const override { return "Deletion MUC"; }
};

class binary_search_muc : public minimal_unsat_core {

  void qx(const expr::ExprVector &target, unsigned begin, unsigned end,
          bool skip, expr::ExprVector &out);

  unsigned m_timeout; /*seconds*/

public:
  binary_search_muc(solver::Solver &solver, unsigned timeout);

  void run(const expr::ExprVector &formula, expr::ExprVector &out) override;

  std::string get_name() const override { return "QuickXplain"; }
};

} // end namespace path_bmc
} // end namespace seahorn
