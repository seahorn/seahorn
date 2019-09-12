#pragma once
/* Generic API for a solver */

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/Smt/Model.hh"

namespace seahorn {
namespace solver {

typedef std::map<std::string, std::string> solver_options;

class Solver {
  solver_options *d_options;
public:
  
  /** Result of the check */
  enum result {
    /** Formula is satisfiable */
    SAT,
    /** Formula is unsatisfiable */
    UNSAT,
    /** The result is unknown */
    UNKNOWN,
    /** There was an error    */
    ERROR,
  };

  /* assert a formula; sally includes a type here */
  virtual bool add(expr::Expr exp) = 0;
  
  /** Check for satisfiability */
  virtual result check() = 0;
  
  /** Push a context */
  virtual void push() = 0;
  
  /** Pop a context */
  virtual void pop() = 0;

  /** Get a model */
  virtual model *get_model() = 0;
  
  
  Solver(solver_options *options): d_options(options) { }
};
}
}
