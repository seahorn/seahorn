#ifdef WITH_YICES2
#include <gmp.h>
#include "yices.h"

#include "seahorn/Expr/ExprVisitor.hh"
#include "seahorn/Expr/Smt/MarshalYices.hh"
#include "seahorn/Expr/Smt/Yices2ModelImpl.hh"
#include "seahorn/Expr/Smt/Yices2SolverImpl.hh"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

#include <vector>

using namespace expr;

namespace seahorn {
namespace solver {

static void report_fatal_error(std::string const &s) {
  llvm::report_fatal_error(llvm::StringRef(s)); 
}

/* flag to indicate library status; we are single threaded so we can be lazy. */
static bool s_yices_lib_initialized = false;


inline void yices_library_initialize(void){
  if( !s_yices_lib_initialized ){
    s_yices_lib_initialized = true;
    yices_init();
  }
}

yices_solver_impl::yices_solver_impl(expr::ExprFactory &efac, const char *logic,
                                     solver_options opts)
    : Solver(), d_efac(efac) {

  yices_library_initialize();
  /* the yices configuration structure */
  ctx_config_t *cfg = yices_new_config();
  if (logic != nullptr) {
    int32_t res = yices_default_config_for_logic(cfg, logic);
    if (res) {
      WARN << "Warning: logic type [" << logic << "] not supported by Yices2;";
    }
  }
  if (!opts.empty()){
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

namespace {
/// -- true iff the array-term skeleton (stores and ites) has a const-array
/// -- leaf, i.e. the term cannot be encoded for yices without a lambda
bool hasConstArrayLeaf(Expr a) {
  while (true) {
    if (isOpX<CONST_ARRAY>(a))
      return true;
    if (isOpX<STORE>(a)) {
      a = a->arg(0);
      continue;
    }
    if (isOpX<ITE>(a))
      return hasConstArrayLeaf(a->arg(1)) || hasConstArrayLeaf(a->arg(2));
    return false;
  }
}

/// -- push select(arr, idx) through the store/ite skeleton of arr:
/// -- select-over-store becomes an index-equality ite, select-over-ite
/// -- distributes into the branches, and select-over-const-array yields the
/// -- default value. Leaves that are plain array terms keep a plain select.
Expr expandSelectOverConstArray(Expr arr, Expr idx, ExprMap &memo) {
  auto it = memo.find(arr);
  if (it != memo.end())
    return it->second;
  Expr res;
  if (isOpX<CONST_ARRAY>(arr))
    res = arr->right();
  else if (isOpX<STORE>(arr))
    res = boolop::lite(mk<EQ>(idx, arr->arg(1)), arr->arg(2),
                       expandSelectOverConstArray(arr->arg(0), idx, memo));
  else if (isOpX<ITE>(arr))
    res = boolop::lite(arr->arg(0),
                       expandSelectOverConstArray(arr->arg(1), idx, memo),
                       expandSelectOverConstArray(arr->arg(2), idx, memo));
  else
    res = op::array::select(arr, idx);
  memo[arr] = res;
  return res;
}

/// -- rewrite every select whose store/ite skeleton bottoms out in a
/// -- const-array into an ite cascade. Yices contexts cannot assert lambda
/// -- terms, which is the only encoding the marshaller has for const-arrays;
/// -- selects over havoc'd (non-const) memories are left untouched.
Expr rewriteConstArraySelects(Expr e, ExprMap &cache) {
  if (e->arity() == 0)
    return e;
  auto it = cache.find(e);
  if (it != cache.end())
    return it->second;

  ExprVector kids;
  kids.reserve(e->arity());
  bool changed = false;
  for (auto b = e->args_begin(), be = e->args_end(); b != be; ++b) {
    Expr kid = rewriteConstArraySelects(Expr(*b), cache);
    changed |= (kid.get() != *b);
    kids.push_back(kid);
  }
  Expr res = changed ? e->efac().mkNary(e->op(), kids.begin(), kids.end()) : e;
  if (isOpX<SELECT>(res) && hasConstArrayLeaf(res->left())) {
    ExprMap memo;
    res = expandSelectOverConstArray(res->left(), res->right(), memo);
  }
  cache[e] = res;
  return res;
}
} // namespace

bool yices_solver_impl::add(expr::Expr exp){
  ExprMap rw_cache;
  exp = rewriteConstArraySelects(exp, rw_cache);
  // -- debug aid: dump assertions in which a const-array survives the
  // -- rewrite (yices cannot assert them; see rewriteConstArraySelects)
  if (std::getenv("SEA_DEBUG_DUMP_CONST_ARRAY")) {
    std::vector<Expr> matches;
    expr::filter(
        exp, [](Expr e) { return isOpX<CONST_ARRAY>(e); },
        std::back_inserter(matches));
    if (!matches.empty()) {
      llvm::errs() << "=== assertion with CONST_ARRAY (" << matches.size()
                   << ") ===\n"
                   << *exp << "\n";
    }
  }
  term_t yt = marshal_yices::encode_term(exp, get_cache());
  if (yt == NULL_TERM){
    std::string str;  
    raw_string_ostream str_os(str);      
    str_os << "yices_solver_impl::add:  failed to encode: " << *exp << "\n";
    report_fatal_error(str_os.str());
  }
  int32_t errcode = yices_assert_formula(d_ctx, yt);
  if (errcode == -1){
    std::string str;      
    raw_string_ostream str_os(str);          
    str_os << "yices_solver_impl::add:  yices_assert_formula failed: "
	   << yices::error_string() << "\n";
    report_fatal_error(str_os.str());    
  }
  return true;
}

/** Check for satisfiability */
SolverResult yices_solver_impl::check(){
  d_last_assumptions.clear();
  
  //could have a param_t field for this call.
  smt_status_t stat = yices_check_context(d_ctx, nullptr);
  switch(stat){
  case STATUS_UNSAT: return SolverResult::UNSAT;
  case STATUS_SAT: return SolverResult::SAT;
  case STATUS_UNKNOWN: return SolverResult::UNKNOWN;
  case STATUS_INTERRUPTED: return SolverResult::UNKNOWN;
  case STATUS_ERROR: return SolverResult::ERROR;
  default: return SolverResult::UNKNOWN;
  }
}

SolverResult yices_solver_impl::check_with_assumptions(const expr_const_it_range& lits) {
  d_last_assumptions.clear();
  
  std::vector<term_t> y_lits;
  for (auto lit: lits) {
    term_t y_lit = marshal_yices::encode_term(lit, get_cache());
    d_last_assumptions.insert({y_lit, lit});
    if (y_lit == NULL_TERM){
      std::string str;        
      raw_string_ostream str_os(str);  
      str_os << "yices_solver_impl::check_with_assumptions:  failed to encode: "
	     << *lit << "\n";
      report_fatal_error(str_os.str());      
    }
    y_lits.push_back(y_lit);
  }

  smt_status_t stat = yices_check_context_with_assumptions(d_ctx, nullptr,
							   y_lits.size(), &y_lits[0]);
  switch(stat){
  case STATUS_UNSAT: return SolverResult::UNSAT;
  case STATUS_SAT: return SolverResult::SAT;
  case STATUS_UNKNOWN: return SolverResult::UNKNOWN;
  case STATUS_INTERRUPTED: return SolverResult::UNKNOWN;
  case STATUS_ERROR: return SolverResult::ERROR;
  default: return SolverResult::UNKNOWN;
  }
}

/** Return an unsatisfiable core */
void yices_solver_impl::unsat_core(ExprVector& out){
  term_vector_t v;
  yices_init_term_vector(&v);
  int32_t errcode = yices_get_unsat_core(d_ctx, &v);
  if (errcode == -1) {
    std::string str;  
    raw_string_ostream str_os(str);  
    str_os << "yices_solver_impl::unsat_core: the solver is not unsat";
    report_fatal_error(str_os.str());
  }
  for (unsigned i=0, e=v.size; i<e; ++i) {
    auto it = d_last_assumptions.find(v.data[i]);
    if (it == d_last_assumptions.end()) {
      std::string str;        
      raw_string_ostream str_os(str);  
      str_os << "yices_solver_impl::unsat_core: term in the unsat core is not an assumption\n";
      report_fatal_error(str_os.str());      
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

void yices_solver_impl::to_smt_lib(raw_ostream& o) {
  errs() << "Warning: yices::to_smt_lib is not implemented\n";
}

}
}
#endif
