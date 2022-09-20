#ifdef WITH_YICES2
#pragma once

#include "seahorn/Expr/Smt/Solver.hh"
#include "seahorn/Support/SeaLog.hh"
#include "yices.h"

#include <map>

namespace llvm {
class raw_ostream;
}

namespace seahorn {
namespace solver {

namespace yices {
inline std::string error_string(){
  char* emsg = yices_error_string();
  std::string res(emsg);
  yices_free_string(emsg);
  return res;
}
}

/* the yices solver; actually a yices context. */
class yices_solver_impl : public Solver {
public:
  
  using model_ref = typename Solver::model_ref;
  
  using ycache_t = std::map<expr::Expr, term_t>;

  using solver_options = std::map<std::string, std::string>;
  
private:
  
  using assumptions_map_t = std::unordered_map<term_t, expr::Expr>;

  // ctx_config_t *d_cfg;
  
  /* the context */
  context_t *d_ctx;
  
  expr::ExprFactory &d_efac;
  
  ycache_t d_cache;
  
  /* to build unsat cores: this avoids a decode_term function */
  assumptions_map_t d_last_assumptions;
  
public:
  yices_solver_impl(expr::ExprFactory &efac, const char *logic = nullptr,
                    solver_options opts = solver_options());

  ~yices_solver_impl();

  SolverKind get_kind() const override { return SolverKind::YICES2;}

  bool add(expr::Expr exp) override;

  /** Check for satisfiability */
  SolverResult check() override;

  /** Check with assumptions */
  SolverResult
  check_with_assumptions(const expr_const_it_range &assumptions) override;

  /** Return an unsatisfiable core */
  void unsat_core(expr::ExprVector& out) override; 
  
  /** Push a context */
  void push() override;

  /** Pop a context */
  void pop() override;
  
  /** Get a model */
  model_ref get_model() override;

  /** Clear all assertions */
  void reset() override;

  /** Print asserted formulas to SMT-LIB format **/
  void to_smt_lib(llvm::raw_ostream &o) override;

  ycache_t &get_cache(void);
};
}
}
#endif
