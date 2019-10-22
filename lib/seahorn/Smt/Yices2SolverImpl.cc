#ifdef WITH_YICES2
#include <gmp.h>
#include "yices.h"

#include "seahorn/Expr/Smt/Yices2SolverImpl.hh"
#include "seahorn/Expr/Smt/Yices2ModelImpl.hh"
#include "seahorn/Expr/Smt/MarshalYices.hh"

#include <vector>

using namespace expr;

namespace seahorn {
namespace yices {


/* flag to indicate library status; we are single threaded so we can be lazy. */
static bool s_yices_lib_initialized = false;


inline void yices_library_initialize(void){
  if( !s_yices_lib_initialized ){
    s_yices_lib_initialized = true;
    yices_init();
  }
}

yices_solver_impl::yices_solver_impl(expr::ExprFactory &efac, solver_options opts)
  : Solver(),
    d_efac(efac) {
  
  yices_library_initialize();
  /* the yices configuration structure */
  ctx_config_t *cfg = nullptr;
  
  if (!opts.empty()){
    cfg = yices_new_config();
    /* iterate through the opts map and set the keys */
    for (auto it = opts.begin(), et=opts.end() ; it != et; ++it){
      yices_set_config(cfg, it->first.c_str(), it->second.c_str());
    }
  }

  d_ctx = yices_new_context(cfg);
  
  if (cfg != nullptr){
    yices_free_config(cfg);
  }

}

yices_solver_impl::~yices_solver_impl(){
  yices_free_context(d_ctx);
}


yices_solver_impl::ycache_t& yices_solver_impl::get_cache(void){
  return d_cache;
}


bool yices_solver_impl::add(expr::Expr exp){
  term_t yt = marshal_yices::encode_term(exp, get_cache());
  if (yt == NULL_TERM){
    llvm::errs() << "yices_solver_impl::add:  failed to encode: " << *exp << "\n";
    llvm_unreachable(nullptr);
  }
  int32_t errcode = yices_assert_formula(d_ctx, yt);
  if (errcode == -1){
    llvm::errs() << "yices_solver_impl::add:  yices_assert_formula failed: "
		 << yices::error_string() << "\n";
    llvm_unreachable(nullptr);    
  }
  return true;
}

/** Check for satisfiability */
solver::SolverResult yices_solver_impl::check(){
  d_last_assumptions.clear();
  
  //could have a param_t field for this call.
  smt_status_t stat = yices_check_context(d_ctx, nullptr);
  switch(stat){
  case STATUS_UNSAT: return solver::SolverResult::UNSAT;
  case STATUS_SAT: return solver::SolverResult::SAT;
  case STATUS_UNKNOWN: return solver::SolverResult::UNKNOWN;
  case STATUS_INTERRUPTED: return solver::SolverResult::UNKNOWN;
  case STATUS_ERROR: return solver::SolverResult::ERROR;
  default: return solver::SolverResult::UNKNOWN;
  }
}

solver::SolverResult yices_solver_impl::check_with_assumptions(const ExprVector& a) {
  d_last_assumptions.clear();
  
  std::vector<term_t> ya;
  ya.reserve(a.size());
  for (unsigned i=0, e=a.size();i<e;++i) {
    term_t yt = marshal_yices::encode_term(a[i], get_cache());
    d_last_assumptions.insert({yt, a[i]});
    if (yt == NULL_TERM){
      llvm::errs() << "yices_solver_impl::check_with_assumptions:  failed to encode: "
		   << *a[i] << "\n";
      llvm_unreachable(nullptr);
    }
    ya.push_back(yt);
  }

  smt_status_t stat = yices_check_context_with_assumptions(d_ctx, nullptr, ya.size(), &ya[0]);
  switch(stat){
  case STATUS_UNSAT: return solver::SolverResult::UNSAT;
  case STATUS_SAT: return solver::SolverResult::SAT;
  case STATUS_UNKNOWN: return solver::SolverResult::UNKNOWN;
  case STATUS_INTERRUPTED: return solver::SolverResult::UNKNOWN;
  case STATUS_ERROR: return solver::SolverResult::ERROR;
  default: return solver::SolverResult::UNKNOWN;
  }
}

/** Return an unsatisfiable core */
void yices_solver_impl::unsat_core(ExprVector& out){
  term_vector_t v;
  yices_init_term_vector(&v);
  int32_t errcode = yices_get_unsat_core(d_ctx, &v);
  if (errcode == -1) {
    errs() << "yices_solver_impl::unsat_core: the solver is not unsat";
    llvm_unreachable(nullptr);
  }
  for (unsigned i=0, e=v.size; i<e; ++i) {
    auto it = d_last_assumptions.find(v.data[i]);
    if (it == d_last_assumptions.end()) {
      errs() << "yices_solver_impl::unsat_core: term in the unsat core is not an assumption\n";
      llvm_unreachable(nullptr);
    }
    out.push_back(it->second);
  }
  yices_delete_term_vector(&v);
}

/** Push a context */
void yices_solver_impl::push(){
  yices_push(d_ctx);
}

/** Pop a context */
void yices_solver_impl::pop(){
  yices_pop(d_ctx);
}

/** Clear all assertions */
void yices_solver_impl::reset(){
  yices_reset_context(d_ctx);  
}

/** Get a model */
yices_solver_impl::model_ref yices_solver_impl::get_model(){
  model_t *model = yices_get_model(d_ctx, 1); 
  return model_ref(new yices_model_impl(model, *this, d_efac));
}
}
}
#endif
