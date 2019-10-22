#ifdef WITH_YICES2
#pragma once

#include "yices.h"
#include "seahorn/Expr/Smt/Solver.hh"
#include <map>

namespace seahorn {
namespace yices {

static std::string error_string(){
  char* emsg = yices_error_string();
  std::string res(emsg);
  yices_free_string(emsg);
  return res;
}

/* the yices solver; actually a yices context. */
class yices_solver_impl : public solver::Solver {
public:
  
  using model_ref = typename solver::Solver::model_ref;
  
  using ycache_t = std::map<expr::Expr, term_t>;

private:
  
  using assumptions_map_t = std::unordered_map<term_t, expr::Expr>;
  
  ctx_config_t *d_cfg;
  
  /* the context */
  context_t *d_ctx;
  
  expr::ExprFactory &d_efac;
  
  ycache_t d_cache;
  
  /* to build unsat cores: this avoids a decode_term function */
  assumptions_map_t d_last_assumptions;
  
public:
  
  /* how should we set the default logic? */
  yices_solver_impl(seahorn::solver::solver_options *opts, expr::ExprFactory &efac);

  ~yices_solver_impl();

  solver::SolverKind get_kind() const { return solver::SolverKind::YICES2;}
  
  bool add(expr::Expr exp);
  
  /** Check for satisfiability */
  solver::SolverResult check();

  /** Check with assumptions */
  solver::SolverResult check_with_assumptions(const expr::ExprVector& assumptions);

  /** Return an unsatisfiable core */
  void unsat_core(expr::ExprVector& out); 
  
  /** Push a context */
  void push();
  
  /** Pop a context */
  void pop();
  
  /** Get a model */
  model_ref get_model();

  /** Clear all assertions */
  void reset();
  
  ycache_t& get_cache(void);
  
  
};
}
}
#endif
