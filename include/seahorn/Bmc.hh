#ifndef __BMC__HH_
#define __BMC__HH_

#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include "boost/container/flat_set.hpp"
#include "boost/logic/tribool.hpp"

#include "seahorn/CallUtils.hh"
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/HexDump.hh"
#include "seahorn/Expr/Smt/EZ3.hh"

#include "seahorn/Analysis/CutPointGraph.hh"
#include "seahorn/OperationalSemantics.hh"

namespace seahorn {
using namespace expr;

namespace bmc_impl {
/// true if I is a call to a void function
bool isCallToVoidFn(const llvm::Instruction &I);
/// computes an implicant of f (interpreted as a conjunction) that
/// contains the given model
template <typename model_ref>
void get_model_implicant(const ExprVector &f, model_ref model, ExprVector &out,
                         ExprMap &active_bool_map);
// out is a minimal unsat core f based on assumptions
void unsat_core(ZSolver<EZ3> &solver, const ExprVector &f,
                bool simplify, ExprVector &out);

template <typename Out>
void dump_evaluated_inst(const Instruction &inst, Expr v, Out &out,
                         bool shadow_mem);
} // namespace bmc_impl

template <class Engine, typename Model> class BmcTrace;
class BmcEngine;
using ZModelRef = ZModel<EZ3>;
using ZBmcTraceTy = BmcTrace<BmcEngine, ZModelRef>;
class BmcEngine {
protected:
  /// symbolic operational semantics
  OperationalSemantics &m_sem;
  /// \brief Context for OperationalSemantics
  OpSemContextPtr m_semCtx;

  /// expression factory
  ExprFactory &m_efac;

  /// last result
  boost::tribool m_result;

  /// cut-point trace
  SmallVector<const CutPoint *, 8> m_cps;

  /// symbolic states corresponding to m_cps
  std::vector<SymStore> m_states;
  /// edge-trace corresponding to m_cps
  SmallVector<const CpEdge *, 8> m_edges;

  const CutPointGraph *m_cpg;
  const llvm::Function *m_fn;

  ZSolver<EZ3> m_smt_solver;

  SymStore m_ctxState;
  /// path-condition for m_cps
  ExprVector m_side;

public:
  BmcEngine(OperationalSemantics &sem, EZ3 &zctx);
  void addCutPoint(const CutPoint &cp);

  virtual OperationalSemantics &sem() { return m_sem; }

  EZ3 &zctx() { return m_smt_solver.getContext(); }

  /// constructs the path condition
  virtual void encode(bool assert_formula = true);

  /// checks satisfiability of the path condition
  virtual boost::tribool solve();

  /// get model if side condition evaluated to sat.
  virtual ZModel<EZ3> getModel() {
    assert((bool)result());
    return m_smt_solver.getModel();
  }

  /// Returns the BMC trace (if available)
  ZBmcTraceTy getTrace();

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

  // given an Expr encoding of memory map, return only the raw mem part
  Expr getRawMem(Expr e) {
    if (!m_semCtx)
      return Expr();
    return m_semCtx->getRawMem(e);
  }

  /// Dump unsat core
  /// Exposes internal details. Intendent to be used for debugging only
  virtual void unsatCore(ExprVector &out);

  /// output current path condition in SMT-LIB2 format
  virtual raw_ostream &toSmtLib(raw_ostream &out);

  /// returns the latest result from solve()
  boost::tribool result() { return m_result; }

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

template <class Engine, class Model> class BmcTrace {
  Engine &m_bmc;
  Model m_model;

  // for trace specific implicant
  ExprVector m_trace;
  ExprMap m_bool_map;

  /// the trace of basic blocks
  SmallVector<const BasicBlock *, 8> m_bbs;

  /// a map from an index of a basic block on a trace to the index
  /// of the corresponding cutpoint in Engine
  SmallVector<unsigned, 8> m_cpId;

  /// cutpoint id corresponding to the given location
  unsigned cpid(unsigned loc) const { return m_cpId[loc]; }

  /// true if loc is the first location on a cutpoint edge
  bool isFirstOnEdge(unsigned loc) const {
    return loc == 0 || cpid(loc - 1) != cpid(loc);
  }

  void constructTrace();

public:
  BmcTrace(Engine &bmc, Model model) : m_bmc(bmc), m_model(model) {
    constructTrace();
  }

  BmcTrace(const BmcTrace &other)
      : m_bmc(other.m_bmc), m_model(other.m_model), m_bbs(other.m_bbs),
        m_cpId(other.m_cpId) {}

  /// underlying BMC engine
  Engine &engine() { return m_bmc; }
  /// The number of basic blocks in the trace
  unsigned size() const { return m_bbs.size(); }

  /// The basic block at a given location
  const llvm::BasicBlock *bb(unsigned loc) const { return m_bbs[loc]; }

  /// The value of the instruction at the given location
  Expr symb(unsigned loc, const llvm::Value &val);

  Expr eval(unsigned loc, const llvm::Value &inst, bool complete = false);

  Expr eval(unsigned loc, Expr u, bool complete = false);

  template <typename Out> Out &print(Out &out);

  ExprVector &get_implicant_formula() { return m_trace; }
  ExprMap &get_implicant_bools_map() { return m_bool_map; }

  const ExprVector &get_implicant_formula() const { return m_trace; }
  const ExprMap &get_implicant_bools_map() const { return m_bool_map; }
};
} // namespace seahorn
// implementation
#include "seahorn/BmcImpl.hh"
#endif
