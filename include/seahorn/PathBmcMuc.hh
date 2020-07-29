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
class minimalUnsatCore {
protected:
  solver::Solver &m_solver;

public:
  minimalUnsatCore(solver::Solver &solver) : m_solver(solver) {}

  virtual void run(const expr::ExprVector &f, expr::ExprVector &core) = 0;

  virtual std::string getName(void) const = 0;
};

class MucWithAssumptions : public minimalUnsatCore {

  void unsat_core(const expr::ExprVector &f, bool simplify,
                  expr::ExprVector &out);

public:
  MucWithAssumptions(solver::Solver &solver);

  void run(const expr::ExprVector &f, expr::ExprVector &core) override;

  std::string getName(void) const override { return "MUC with assumptions"; }
};

class MucBinarySearch;

class MucDeletion : public minimalUnsatCore {

  friend class MucBinarySearch;

  typedef expr::ExprVector::const_iterator const_iterator;

  solver::SolverResult check(const_iterator it, const_iterator et,
                             const expr::ExprVector &assumptions);

  void run(const expr::ExprVector &f, const expr::ExprVector &assumptions,
           expr::ExprVector &out);

  unsigned m_timeout; /*seconds*/

public:
  MucDeletion(solver::Solver &solver, unsigned timeout);

  void run(const expr::ExprVector &f, expr::ExprVector &out) override;

  std::string getName() const override { return "Deletion MUC"; }
};

class MucBinarySearch : public minimalUnsatCore {

  void qx(const expr::ExprVector &target, unsigned begin, unsigned end,
          bool skip, expr::ExprVector &out);

  unsigned m_timeout; /*seconds*/

public:
  MucBinarySearch(solver::Solver &solver, unsigned timeout);

  void run(const expr::ExprVector &formula, expr::ExprVector &out) override;

  std::string getName() const override { return "QuickXplain"; }
};

} // end namespace path_bmc
} // end namespace seahorn
