#pragma once

#include "seahorn/Expr/Smt/Solver.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Expr/Smt/Z3ModelImpl.hh"

namespace seahorn {
namespace z3 {

class z3_solver_impl : public solver::Solver {
  std::unique_ptr<ZSolver<EZ3>> m_solver;
  solver::SolverResult m_last_result;
  
public:

  using model_ref = typename solver::Solver::model_ref;
  
  z3_solver_impl(seahorn::solver::solver_options *opts, EZ3 &zctx)
    : solver::Solver(opts)
    , m_solver(new ZSolver<EZ3>(zctx))
    , m_last_result(solver::SolverKind::UNKNOWN) {}

  solver::SolverKind get_kind() const { return solver::SolverKind::Z3;}
  
  virtual bool add(expr::Expr exp) override {
    m_solver->assertExpr(exp);
    return true;
  }
  
  /** Check for satisfiability */
  virtual solver::SolverResult check() override {
    auto res = m_solver->solve();
    if (res) {
      m_last_result = solver::SolverKind::SAT;
    } else if (!res) {
      m_last_result = solver::SolverKind::UNSAT;
    } else {
      m_last_result = solver::SolverKind::UNKNOWN; 
    }
    return m_last_result;
  }

  virtual solver::SolverResult check_with_assumptions(const expr::ExprVector& a) override {
    auto res = m_solver->solveAssuming(a);
    if (res) {
      m_last_result = solver::SolverKind::SAT;
    } else if (!res) {
      m_last_result = solver::SolverKind::UNSAT;
    } else {
      m_last_result = solver::SolverKind::UNKNOWN; 
    }
    return m_last_result;
  }

  virtual void unsat_core(expr::ExprVector& out) override {
    m_solver->unsatCore(std::back_inserter(out));
  }
  
  /** Push a context */
  virtual void push() override {
    m_solver->push();
  }
  
  /** Pop a context */
  virtual void pop() override {
    m_solver->pop();
  }

  /** Clear all assertions */
  virtual void reset() override {
    m_solver->reset();
  }
  
  /** Get a model */
  virtual model_ref get_model() override {
    assert(m_last_result == SAT);
    ZModel<EZ3> model = m_solver->getModel();
    return model_ref(new z3_model_impl(model));
  }
  
};
}
}
