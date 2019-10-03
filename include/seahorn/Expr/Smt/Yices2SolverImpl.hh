#ifdef WITH_YICES2
#pragma once

#include "yices.h"

#include "seahorn/Expr/Smt/Solver.hh"

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
  
  using ycache_t = std::map<expr::Expr, term_t>;
  
  ctx_config_t *d_cfg;
  
  /* the context */
  context_t *d_ctx;
  
  expr::ExprFactory &d_efac;
  
  ycache_t d_cache;
  
public:

  using model_ref = typename solver::Solver::model_ref;
  
  /* how should we set the default logic? */
  yices_solver_impl(seahorn::solver::solver_options *opts, expr::ExprFactory &efac);

  ~yices_solver_impl();
  
  bool add(expr::Expr exp);
  
  /** Check for satisfiability */
  solver::Solver::result check();
  
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
