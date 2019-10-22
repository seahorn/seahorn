#pragma once
/* Generic API for a solver */

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/Smt/Model.hh"

namespace seahorn {
namespace solver {

typedef std::map<std::string, std::string> solver_options;

/** Kind of solver **/
enum class SolverKind { Z3 , YICES2};

/** Result of the check */
enum class SolverResult {
  /** Formula is satisfiable */
  SAT,
  /** Formula is unsatisfiable */
  UNSAT,
  /** The result is unknown */
  UNKNOWN,
  /** There was an error    */
  ERROR,
};

class Solver {
  solver_options d_options;
public:
  

  using model_ref = std::shared_ptr<Model>;
  
  Solver(solver_options options): d_options(options) { }
  
  virtual ~Solver() {}

  /* Tell the underlying solver without rtti */
  virtual SolverKind get_kind() const = 0;
  
  /* assert a formula */
  virtual bool add(expr::Expr exp) = 0;
  
  /** Check for satisfiability */
  virtual SolverResult check() = 0;

  /** Check for satisfiability */
  virtual SolverResult check_with_assumptions(const expr::ExprVector& a) = 0;

  /** Return an unsatisfiable core */
  virtual void unsat_core(expr::ExprVector& out) = 0;
  
  /** Push a context */
  virtual void push() = 0;
  
  /** Pop a context */
  virtual void pop() = 0;

  /** Get a model */
  virtual model_ref get_model() = 0;

  /** Clear all assertions */
  virtual void reset() = 0;
    
};
}
}
