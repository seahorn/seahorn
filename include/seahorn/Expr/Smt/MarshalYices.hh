#ifdef WITH_YICES2
#pragma once

#include <gmp.h>
#include "yices.h"
#include "seahorn/Expr/ExprLlvm.hh"
#include <map>

namespace seahorn {
namespace solver {

using ycache_t = std::map<expr::Expr, term_t>;

class marshal_yices {
  
public:

  static term_t encode_term(expr::Expr exp, ycache_t &cache);
  
  static type_t encode_type(expr::Expr exp);

  static expr::Expr eval(expr::Expr expr,  expr::ExprFactory &efac,
			 ycache_t &cache, bool complete, model_t *model);
  
  static expr::Expr decode_type(type_t yty, expr::ExprFactory &efac);
  
private:
  
  static expr::Expr decode_yval(yval_t &yval,  expr::ExprFactory &efac,
				model_t *model, bool isArray, expr::Expr domain,
				expr::Expr range);
  
};
}
}
#endif
