#pragma once

#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#include "boost/logic/tribool.hpp"

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Expr/Smt/Solver.hh"
#include "seahorn/Expr/Smt/Z3SolverImpl.hh"
#ifdef WITH_YICES2
#include "seahorn/Expr/Smt/Yices2SolverImpl.hh"
#endif

#include "seahorn/Analysis/CutPointGraph.hh"
#include "seahorn/OperationalSemantics.hh"

namespace seahorn {
using namespace expr;

namespace solver_bmc_impl {
/// true if I is a call to a void function
bool isCallToVoidFn(const llvm::Instruction &I);
/// computes an implicant of f (interpreted as a conjunction) that
/// contains the given model
void get_model_implicant(const ExprVector &f, solver::Solver::model_ref model,
                         ExprVector &out, ExprMap &active_bool_map);
} // namespace solver_bmc_impl

class SolverBmcTrace;
class SolverBmcEngine {
protected:
  /// symbolic operational semantics
  OperationalSemantics &m_sem;
  /// \brief Context for OperationalSemantics
  OpSemContextPtr m_semCtx;

  /// expression factory
  ExprFactory &m_efac;

  /// last result
  solver::SolverResult m_result;

  /// cut-point trace
  SmallVector<const CutPoint *, 8> m_cps;

  /// symbolic states corresponding to m_cps
  std::vector<SymStore> m_states;
  /// edge-trace corresponding to m_cps
  SmallVector<const CpEdge *, 8> m_edges;

  const CutPointGraph *m_cpg;
  const llvm::Function *m_fn;

  // main solver
  solver::SolverKind m_solver_kind;
  std::unique_ptr<solver::Solver> m_new_smt_solver;
  // simplifying solver that only relies on z3
  // std::unique_ptr<solver::Solver> m_simp_smt_solver;

  SymStore m_ctxState;
  /// path-condition for m_cps
  ExprVector m_side;

public:
  SolverBmcEngine(OperationalSemantics &sem,
                  solver::SolverKind solver_kind = solver::SolverKind::Z3);
  void addCutPoint(const CutPoint &cp);

  virtual OperationalSemantics &sem() { return m_sem; }

  /// constructs the path condition
  virtual void encode(bool assert_formula = true);

  /// checks satisfiability of the path condition
  virtual solver::SolverResult solve();

  /// get model if side condition evaluated to sat.
  virtual solver::Solver::model_ref getModel() {
    assert((bool)result());
    return m_new_smt_solver->get_model();
  }

  /// Returns the BMC trace (if available)
  virtual SolverBmcTrace getTrace();

  Expr getSymbReg(const llvm::Value &v) {
    Expr reg;
    if (m_semCtx) {
      return m_sem.getSymbReg(v, *m_semCtx);
    }
    return reg;
  }

  /// output current path condition in SMT-LIB2 format
  virtual raw_ostream &toSmtLib(raw_ostream &out);

  /// returns the latest result from solve()
  solver::SolverResult result() { return m_result; }

  /// access to expression factory
  ExprFactory &efac() { return m_efac; }

  /// reset the engine
  void reset();

  /// get side condition
  const ExprVector &getFormula() const { return m_side; }

  /// get cut-point trace
  const SmallVector<const CutPoint *, 8> &getCps() const { return m_cps; }

  /// get edges from the cut-point trace
  const SmallVector<const CpEdge *, 8> &getEdges() const { return m_edges; }

  /// get symbolic states corresponding to the cutpoint trace
  std::vector<SymStore> &getStates() { return m_states; }
};

class SolverBmcTrace {
  SolverBmcEngine &m_bmc;

  // ZModel<EZ3> m_model;
  solver::Solver::model_ref m_model;

  // for trace specific implicant
  ExprVector m_trace;
  ExprMap m_bool_map;

  /// the trace of basic blocks
  SmallVector<const BasicBlock *, 8> m_bbs;

  /// a map from an index of a basic block on a trace to the index
  /// of the corresponding cutpoint in SolverBmcEngine
  SmallVector<unsigned, 8> m_cpId;

  /// cutpoint id corresponding to the given location
  unsigned cpid(unsigned loc) const { return m_cpId[loc]; }

  /// true if loc is the first location on a cutpoint edge
  bool isFirstOnEdge(unsigned loc) const {
    return loc == 0 || cpid(loc - 1) != cpid(loc);
  }

public:
  SolverBmcTrace(SolverBmcEngine &bmc, solver::Solver::model_ref model);

  SolverBmcTrace(const SolverBmcTrace &other)
      : m_bmc(other.m_bmc), m_model(other.m_model), m_bbs(other.m_bbs),
        m_cpId(other.m_cpId) {}

  /// underlying BMC engine
  SolverBmcEngine &engine() { return m_bmc; }
  /// The number of basic blocks in the trace
  unsigned size() const { return m_bbs.size(); }

  /// The basic block at a given location
  const llvm::BasicBlock *bb(unsigned loc) const { return m_bbs[loc]; }

  /// The value of the instruction at the given location
  Expr symb(unsigned loc, const llvm::Value &inst);
  Expr eval(unsigned loc, const llvm::Value &inst, bool complete = false);
  Expr eval(unsigned loc, Expr v, bool complete = false);
  template <typename Out> Out &print(Out &out);

  ExprVector &get_implicant_formula() { return m_trace; }
  ExprMap &get_implicant_bools_map() { return m_bool_map; }

  const ExprVector &get_implicant_formula() const { return m_trace; }
  const ExprMap &get_implicant_bools_map() const { return m_bool_map; }
};
} // namespace seahorn
