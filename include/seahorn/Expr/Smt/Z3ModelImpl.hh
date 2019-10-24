#pragma once

#include "seahorn/Expr/Smt/Model.hh"
#include "seahorn/Expr/Smt/EZ3.hh"

namespace seahorn {
namespace solver {

class z3_model_impl: public Model {
  ZModel<EZ3> m_model;
  
public:
  
  z3_model_impl(ZModel<EZ3> model): m_model(model) {}
  
  virtual expr::Expr eval(expr::Expr expr, bool complete) override {
    return m_model.eval(expr, complete);
  }

  virtual void print(llvm::raw_ostream& o) const override {
    o << *(const_cast<ZModel<EZ3>*>(&m_model));
  }
  
};
}
}
