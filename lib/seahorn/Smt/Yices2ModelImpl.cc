#ifdef WITH_YICES2

#include "yices.h"

#include "seahorn/Expr/Smt/Model.hh"
#include "seahorn/Expr/Smt/MarshalYices.hh"
#include "seahorn/Expr/Smt/Yices2ModelImpl.hh"

namespace seahorn {
namespace solver {

/* printing defaults */
uint32_t yices_model_impl::width   = 80;
uint32_t yices_model_impl::height  = 100;
uint32_t yices_model_impl::offset  = 0;


yices_model_impl::yices_model_impl(model_t *model, yices_solver_impl &solver,
				   expr::ExprFactory &efac)
  : d_model(model),
    d_solver(solver),
    d_efac(efac)
{  }

yices_model_impl::~yices_model_impl(){
  yices_free_model(d_model);
}

expr::Expr yices_model_impl::eval(expr::Expr exp, bool complete){
  return marshal_yices::eval(exp,  d_efac, d_solver.get_cache(), complete, d_model);
}

void yices_model_impl::print(llvm::raw_ostream& o) const {
  char* model_as_string = yices_model_to_string(d_model, width, height, offset);
  o << model_as_string;
  yices_free_string(model_as_string);
}

}
}
#endif
