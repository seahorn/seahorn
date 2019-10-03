#pragma once

#include "seahorn/Expr/Smt/Model.hh"
#include "seahorn/Expr/Smt/Z3.hh"

namespace seahorn {
namespace z3 {

class z3_model_impl: public solver::model {
  ufo::ZModel<ufo::EZ3> m_model;
  
public:
  
  z3_model_impl(ufo::ZModel<ufo::EZ3> model): m_model(model) {}
  
  virtual expr::Expr eval(expr::Expr expr, bool complete) override {
    return m_model.eval(expr, complete);
  }

  virtual void print(llvm::raw_ostream& o) const override {
    o << *(const_cast<ufo::ZModel<ufo::EZ3>*>(&m_model));
  }
  
};
}
}
