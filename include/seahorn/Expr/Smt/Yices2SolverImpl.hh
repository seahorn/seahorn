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
  
  typedef  std::map<expr::Expr, term_t> ycache_t;
  
  ctx_config_t *d_cfg;
  
  /* the context */
  context_t *d_ctx;
  
  expr::ExprFactory &d_efac;
  
  ycache_t d_cache;
  
public:
  
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
  solver::model *get_model();
  
  
  ycache_t& get_cache(void);
  
  
};
}
}
#endif
