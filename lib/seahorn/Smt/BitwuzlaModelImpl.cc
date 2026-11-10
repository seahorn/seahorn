#ifdef WITH_BITWUZLA

#include "seahorn/Expr/Smt/BitwuzlaModelImpl.hh"
#include "seahorn/Expr/Smt/BitwuzlaSolverImpl.hh"
#include "seahorn/Support/SeaLog.hh"

using namespace expr;

namespace seahorn {
namespace solver {

Expr bitwuzla_model_impl::eval(Expr e, bool /*complete*/) {
  if (auto solver = m_solver.lock())
    return (*solver)->eval_in_model(e, m_generation);
  ERR << "Bitwuzla adapter: a model was used after its solver was destroyed; "
         "it has no values";
  return mk<NONDET>(e->efac());
}

void bitwuzla_model_impl::print(llvm::raw_ostream &o) const {
  if (auto solver = m_solver.lock()) {
    (*solver)->print_model(o, m_generation);
    return;
  }
  ERR << "Bitwuzla adapter: a model was printed after its solver was "
         "destroyed; it has no values";
}

} // namespace solver
} // namespace seahorn

#endif
