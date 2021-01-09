#pragma once

#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Bmc.hh"
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
using namespace solver;

class SolverBmcEngine;
using SolverBmcTraceTy = BmcTrace<SolverBmcEngine, Solver::model_ref>;

class SolverBmcEngine {
protected:
  /// symbolic operational semantics
  OperationalSemantics &m_sem;
  /// \brief Context for OperationalSemantics
  OpSemContextPtr m_semCtx;

  /// expression factory
  ExprFactory &m_efac;

  /// last result
  SolverResult m_result;

  /// cut-point trace
  SmallVector<const CutPoint *, 8> m_cps;

  /// symbolic states corresponding to m_cps
  std::vector<SymStore> m_states;
  /// edge-trace corresponding to m_cps
  SmallVector<const CpEdge *, 8> m_edges;

  const CutPointGraph *m_cpg;
  const llvm::Function *m_fn;

  // main solver
  SolverKind m_solver_kind;
  std::unique_ptr<Solver> m_new_smt_solver;
  // simplifying solver that only relies on z3
  // std::unique_ptr<Solver> m_simp_smt_solver;

  SymStore m_ctxState;
  /// path-condition for m_cps
  ExprVector m_side;

public:
  SolverBmcEngine(OperationalSemantics &sem,
                  SolverKind solver_kind = SolverKind::Z3);
  void addCutPoint(const CutPoint &cp);

  virtual OperationalSemantics &sem() { return m_sem; }

  /// constructs the path condition
  virtual void encode(bool assert_formula = true);

  /// checks satisfiability of the path condition
  virtual SolverResult solve();

  /// get model if side condition evaluated to sat.
  virtual Solver::model_ref getModel() {
    assert((bool)result());
    return m_new_smt_solver->get_model();
  }

  /// Returns the BMC trace (if available)
  SolverBmcTraceTy getTrace();

  Expr getSymbReg(const llvm::Value &v) {
    Expr reg;
    if (m_semCtx) {
      return m_sem.getSymbReg(v, *m_semCtx);
    }
    return reg;
  }

  // given an Expr encoding of pointer, return only addressable part
  Expr getPtrAddressable(Expr e) {
    if (!m_semCtx)
      return Expr();
    return m_semCtx->ptrToAddr(e);
  }

  Expr getRawMem(Expr e) {
    if (!m_semCtx)
      return Expr();
    return m_semCtx->getRawMem(e);
  }

  /// output current path condition in SMT-LIB2 format
  virtual raw_ostream &toSmtLib(raw_ostream &out);

  /// returns the latest result from solve()
  SolverResult result() { return m_result; }

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
} // namespace seahorn
