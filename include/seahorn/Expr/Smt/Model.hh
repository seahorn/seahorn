#pragma once
/* Generic API for a model */

#include "seahorn/Expr/ExprLlvm.hh"

namespace seahorn {
namespace solver {

class model {
public:
  virtual ~model(){};
  
  virtual expr::Expr eval(expr::Expr expr, bool complete) = 0;

  virtual void print(llvm::raw_ostream& o) const = 0;
  
  friend llvm::raw_ostream& operator<<(llvm::raw_ostream &o, const model &model) {
    model.print(o);
    return o;
  }
};
}
}
