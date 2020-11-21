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
#include "seahorn/Expr/HexDump.hh"
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/Smt/EZ3.hh"

#include "seahorn/Analysis/CutPointGraph.hh"
#include "seahorn/OperationalSemantics.hh"

namespace seahorn {
using namespace expr;
using ZModel_ref = std::shared_ptr<ZModel<EZ3>>;

namespace bmc_impl {
/// true if I is a call to a void function
bool isCallToVoidFn(const llvm::Instruction &I);
/// computes an implicant of f (interpreted as a conjunction) that
/// contains the given model
template <typename model_ref>
void get_model_implicant(const ExprVector &f, model_ref model, ExprVector &out,
                         ExprMap &active_bool_map) {
  Expr bool_lit = nullptr;
  for (auto v : f) {
    // -- break IMPL into an OR
    // -- OR into a single disjunct
    // -- single disjunct into an AND
    if (isOpX<IMPL>(v)) {
      assert(v->arity() == 2);
      Expr v0 = model->eval(v->arg(0), false);
      Expr a0 = v->arg(0);
      if (isOpX<FALSE>(v0))
        continue;
      else if (isOpX<TRUE>(v0)) {
        v = mknary<OR>(mk<FALSE>(v0->efac()), ++(v->args_begin()),
                       v->args_end());
        bool_lit = a0;
      } else
        continue;
    }

    if (isOpX<OR>(v)) {
      for (unsigned i = 0; i < v->arity(); ++i)
        if (isOpX<TRUE>(model->eval(v->arg(i), false))) {
          v = v->arg(i);
          break;
        }
    }

    if (isOpX<AND>(v)) {
      for (unsigned i = 0; i < v->arity(); ++i) {
        out.push_back(v->arg(i));
        if (bool_lit)
          active_bool_map[v->arg(i)] = bool_lit;
      }
    } else {
      out.push_back(v);
      if (bool_lit)
        active_bool_map[v] = bool_lit;
    }
  }
}
// out is a minimal unsat core f based on assumptions
void unsat_core(ZSolver<EZ3> &solver, const ExprVector &f,
                bool simplify, ExprVector &out);

template <typename Out>
void dump_evaluated_inst(const Instruction &inst, Expr v, Out &out,
                         bool shadow_mem);
} // namespace bmc_impl

template <class Engine, typename Model> class BmcTrace;
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
  template <class Engine, class Model>
  BmcTrace<Engine, Model> getTrace();

  Expr getSymbReg(const llvm::Value &v) {
    Expr reg;
    if (m_semCtx) {
      return m_sem.getSymbReg(v, *m_semCtx);
    }
    return reg;
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

template <class Engine, class Model>
class BmcTrace {
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

  void constructTrace() {
    // assert ((bool)bmc.result ());
    // m_model = bmc.getModel ();

    // construct an implicant of the side condition
    m_trace.reserve(m_bmc.getFormula().size());
    ExprMap bool_map /*unused*/;
    bmc_impl::get_model_implicant(m_bmc.getFormula(), m_model, m_trace,
                                         m_bool_map);
    boost::container::flat_set<Expr> implicant(m_trace.begin(), m_trace.end());

    // construct the trace

    // -- reference to the first state
    auto st = m_bmc.getStates().begin();
    // -- reference to the fist cutpoint in the trace
    unsigned id = 0;
    for (const CpEdge *edg : m_bmc.getEdges()) {
      LOG("cex", errs() << "";);

      assert(&(edg->source()) == m_bmc.getCps()[id]);
      assert(&(edg->target()) == m_bmc.getCps()[id + 1]);

      SymStore &s = *(++st);
      for (auto it = edg->begin(), end = edg->end(); it != end; ++it) {
        const BasicBlock &BB = *it;

        if (it != edg->begin() &&
            implicant.count(s.eval(m_bmc.getSymbReg(BB))) <= 0)
          continue;

        m_bbs.push_back(&BB);
        m_cpId.push_back(id);
      }
      // -- next basic block corresponds to the next cutpoint
      id++;
    }

    // -- last block on the edge
    const SmallVector<const CpEdge *, 8> &edges = m_bmc.getEdges();
    if (!edges.empty()) {
      m_bbs.push_back(&edges.back()->target().bb());
      m_cpId.push_back(id);
    } else {
      const SmallVector<const CutPoint *, 8> &cps = m_bmc.getCps();
      assert(cps.size() == 1);
      // special case of trivial counterexample. The counterexample is
      // completely contained within the first cutpoint
      m_bbs.push_back(&cps[0]->bb());
      m_cpId.push_back(0);
    }
  }

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
  Expr symb(unsigned loc, const llvm::Value &val) {
    // assert (cast<Instruction>(&val)->getParent () == bb(loc));

    if (!m_bmc.sem().isTracked(val))
      return Expr();
    if (isa<Instruction>(val) &&
        bmc_impl::isCallToVoidFn(cast<Instruction>(val)))
      return Expr();
    Expr u = m_bmc.getSymbReg(val);

    unsigned stateidx = cpid(loc);
    // -- all registers except for PHI nodes at the entry to an edge
    // -- get their value at the end of the edge
    if (!(isa<PHINode>(val) && isFirstOnEdge(loc)))
      stateidx++;
    // -- out of bounds, no value in the model
    if (stateidx >= m_bmc.getStates().size())
      return Expr();

    SymStore &store = m_bmc.getStates()[stateidx];
    return store.eval(u);
  }

  Expr eval(unsigned loc, const llvm::Value &inst, bool complete = false) {
    Expr v = symb(loc, inst);
    if (v)
      v = m_model->eval(v, complete);
    return v;
  }

  Expr eval(unsigned loc, Expr u, bool complete = false) {

    unsigned stateidx = cpid(loc);
    stateidx++;
    // -- out of bounds, no value in the model
    if (stateidx >= m_bmc.getStates().size())
      return Expr();

    SymStore &store = m_bmc.getStates()[stateidx];
    Expr v = store.eval(u);
    return m_model->eval(v, complete);
  }

  template <typename Out> Out &print(Out &out) {
    out << "Begin trace \n";
    for (unsigned loc = 0; loc < size(); ++loc) {
      const BasicBlock &BB = *bb(loc);
      out << BB.getName() << ": \n";

      for (auto &I : BB) {
        if (const DbgValueInst *dvi = dyn_cast<DbgValueInst>(&I)) {
          if (dvi->getValue() && dvi->getVariable()) {
            if (out.has_colors())
              out.changeColor(raw_ostream::RED);
            DILocalVariable *var = dvi->getVariable();
            out << "  " << var->getName() << " = ";
            if (dvi->getValue()->hasName())
              out << dvi->getValue()->getName();
            else
              out << *dvi->getValue();

            auto val = eval(loc, *dvi->getValue());
            if (val)
              out << " " << *val;

            out << "\n";
            out.resetColor();
          }
          continue;
        }

        bool print_inst = true;
        bool shadow_mem = false;
        if (auto *ci = dyn_cast<CallInst>(&I)) {
          const Function *f = getCalledFunction(*ci);
          if (f && f->getName().equals("seahorn.fn.enter")) {
            if (ci->getDebugLoc()) {
              if (DISubprogram *fnScope =
                      getDISubprogram(ci->getDebugLoc().getScope()))
                out << "enter: " << fnScope->getName() << "\n";
            }
            continue;
          } else if (f && f->getName().equals("shadow.mem.init")) {
            print_inst = false;
            shadow_mem = true;
          } else if (f && f->getName().equals("shadow.mem.store")) {
            shadow_mem = true;
          } else if (f && f->getName().equals("sea_printf")) {
            if (out.has_colors())
              out.changeColor(raw_ostream::GREEN);

            if (auto *gep = dyn_cast<GetElementPtrInst>(&*ci->arg_begin())) {
              out << "  " << *gep->getPointerOperand() << "\n";
            }
            for (auto &arg :
                 llvm::make_range(ci->arg_begin() + 1, ci->arg_end())) {
              if (arg->hasName()) {
                out << "  " << arg->getName() << " ";
                auto val = eval(loc, *arg);
                if (val)
                  out << *val;
                else
                  out << *arg;
                out << "\n";
              }
            }
            if (out.has_colors())
              out.resetColor();
          }
        } else if (isa<PHINode>(I)) {
          shadow_mem = I.hasMetadata("shadow.mem");
        }

        if (print_inst) {
          out << I << "\n";
        }

        Expr v = eval(loc, I);
        if (!v)
          continue;

        bmc_impl::dump_evaluated_inst(I, v, out, shadow_mem);

      }
    }
    out << "End trace\n";
    return out;
  }

  ExprVector &get_implicant_formula() { return m_trace; }
  ExprMap &get_implicant_bools_map() { return m_bool_map; }

  const ExprVector &get_implicant_formula() const { return m_trace; }
  const ExprMap &get_implicant_bools_map() const { return m_bool_map; }
};
} // namespace seahorn

#endif
