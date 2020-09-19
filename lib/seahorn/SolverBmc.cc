#include "seahorn/SolverBmc.hh"
#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"
#include "seahorn/UfoOpSem.hh"

#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/Support/CommandLine.h"

#include "boost/container/flat_set.hpp"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/HexDump.hh"
#include "seahorn/Support/SeaDebug.h"

namespace seahorn {
/* use options from Bmc.cc*/
extern bool DumpHex;
extern std::string BmcSmtLogic;
extern std::string BmcSmtTactic;
} // namespace seahorn

namespace seahorn {
SolverBmcEngine::SolverBmcEngine(OperationalSemantics &sem,
                                 solver::SolverKind solver_kind)
    : m_sem(sem), m_efac(sem.efac()), m_result(solver::SolverResult::UNKNOWN),
      m_cpg(nullptr), m_fn(nullptr), m_ctxState(m_efac),
      m_solver_kind(solver_kind) {

  if (m_solver_kind == solver::SolverKind::Z3) {
    LOG("bmc", INFO << "bmc using Z3";);
    z3n_set_param(":model.compact", false);
    if (BmcSmtTactic != "default")
      z3n_set_param(":tactic.default_tactic", BmcSmtTactic.c_str());
    m_new_smt_solver = std::make_unique<solver::z3_solver_impl>(sem.efac());
  } else if (m_solver_kind == solver::SolverKind::YICES2) {
    LOG("bmc", INFO << "bmc using Yices2";);
#ifdef WITH_YICES2
    const char *logic = (BmcSmtLogic == "ALL") ? nullptr : BmcSmtLogic.c_str();
    m_new_smt_solver =
        std::make_unique<solver::yices_solver_impl>(sem.efac(), logic);
#else
    assert(false && "Compile with YICES2_HOME option");
#endif
  } else {
    assert(false && "Unsupported smt solver");
  }
}

void SolverBmcEngine::addCutPoint(const CutPoint &cp) {
  if (m_cps.empty()) {
    m_cpg = &cp.parent();
    m_fn = cp.bb().getParent();
  }

  assert(m_cpg == &cp.parent());
  m_cps.push_back(&cp);
}

solver::SolverResult SolverBmcEngine::solve() {
  encode();
  m_result = m_new_smt_solver->check();
  return m_result;
}

void SolverBmcEngine::encode(bool assert_formula) {

  // -- only run the encoding once
  if (m_semCtx)
    return;

  assert(m_cpg);
  assert(m_fn);

  m_semCtx = m_sem.mkContext(m_ctxState, m_side);
  VCGen vcgen(m_sem);

  // first state is the state in which execution starts
  m_states.push_back(m_semCtx->values());

  // -- for every pair of cut-points
  const CutPoint *prev = nullptr;
  for (const CutPoint *cp : m_cps) {
    if (prev) {
      const CpEdge *edg = m_cpg->getEdge(*prev, *cp);
      assert(edg);
      m_edges.push_back(edg);

      // generate vc for current edge
      vcgen.genVcForCpEdge(*m_semCtx, *edg);
      // store a copy of the state at the end of execution
      m_states.push_back(m_semCtx->values());
    }
    prev = cp;
  }

  if (assert_formula) {
    for (Expr v : m_side)
      m_new_smt_solver->add(v);
  }
}

void SolverBmcEngine::reset() {
  m_cps.clear();
  m_cpg = nullptr;
  m_fn = nullptr;
  m_new_smt_solver->reset();

  m_side.clear();
  m_states.clear();
  m_edges.clear();
}

/// output current path condition in SMT-LIB2 format
raw_ostream &SolverBmcEngine::toSmtLib(raw_ostream &out) {
  encode();
  m_new_smt_solver->to_smt_lib(out);
  return out;
}

SolverBmcTrace SolverBmcEngine::getTrace() {
  assert(m_result == solver::SolverResult::SAT);
  auto model = m_new_smt_solver->get_model();
  return SolverBmcTrace(*this, model);
}

SolverBmcTrace::SolverBmcTrace(SolverBmcEngine &bmc,
                               solver::Solver::model_ref model)
    : m_bmc(bmc), m_model(model /*m_bmc.zctx()*/) {
  // assert ((bool)bmc.result ());
  // m_model = bmc.getModel ();

  // construct an implicant of the side condition
  m_trace.reserve(m_bmc.getFormula().size());
  ExprMap bool_map /*unused*/;
  solver_bmc_impl::get_model_implicant(m_bmc.getFormula(), m_model, m_trace,
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

Expr SolverBmcTrace::symb(unsigned loc, const llvm::Value &val) {
  // assert (cast<Instruction>(&val)->getParent () == bb(loc));

  if (!m_bmc.sem().isTracked(val))
    return Expr();
  if (isa<Instruction>(val) &&
      solver_bmc_impl::isCallToVoidFn(cast<Instruction>(val)))
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

Expr SolverBmcTrace::eval(unsigned loc, const llvm::Value &val, bool complete) {
  Expr v = symb(loc, val);
  if (v)
    v = m_model->eval(v, complete);
  return v;
}

Expr SolverBmcTrace::eval(unsigned loc, Expr u, bool complete) {

  unsigned stateidx = cpid(loc);
  stateidx++;
  // -- out of bounds, no value in the model
  if (stateidx >= m_bmc.getStates().size())
    return Expr();

  SymStore &store = m_bmc.getStates()[stateidx];
  Expr v = store.eval(u);
  return m_model->eval(v, complete);
}

// template <typename Out> Out &SolverBmcTrace::print (Out &out)
template <> raw_ostream &SolverBmcTrace::print(raw_ostream &out) {
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
          out << "\n";
          out.resetColor();
        }
        continue;
      }

      bool print_inst = true;
      bool shadow_mem = false;
      if (const CallInst *ci = dyn_cast<CallInst>(&I)) {
        Function *f = ci->getCalledFunction();
        if (f && f->getName().equals("seahorn.fn.enter")) {
          if (ci->getDebugLoc()) {
            if (DISubprogram *fnScope =
                    getDISubprogram(ci->getDebugLoc().getScope()))
              out << "enter: " << fnScope->getName() << "\n";
          }
          continue;
        } else if (f && f->getName().equals("shadow.mem.init")) {
#if 0
          // disabling since this is not supported by non-legacy
          // OperationalSemantics
          if (out.has_color())
            out.changeColor(raw_ostream::RED);
          int64_t id = shadow_dsa::getShadowId(ci);
          assert(id >= 0);
          Expr memStart = m_bmc.sem().memStart(id);
          Expr u = eval(loc, memStart);
          if (u)
            out << "  " << *memStart << " " << *u << "\n";
          Expr memEnd = m_bmc.sem().memEnd(id);
          u = eval(loc, memEnd);
          if (u)
            out << "  " << *memEnd << " " << *u << "\n";
          out.resetColor();
#endif
          print_inst = false;
          shadow_mem = true;
        } else if (f && f->getName().equals("shadow.mem.store")) {
          shadow_mem = true;
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

      if (out.has_colors())
        out.changeColor(raw_ostream::RED);
      if (DumpHex && shadow_mem) {
        using HD = expr::hexDump::HexDump;
        using SHD = expr::hexDump::StructHexDump;
        out << "  %" << I.getName() << "\n";

        if (isOp<MK_STRUCT>(v)) {
          out << SHD(v);
        } else {
          out << HD(v);
        }

      } else
        out << "  %" << I.getName() << " " << *v;
      const DebugLoc &dloc = I.getDebugLoc();
      if (dloc) {
        if (out.has_colors())
          out.changeColor(raw_ostream::CYAN);
        out << " [" << (*dloc).getFilename() << ":" << dloc.getLine() << "]";
      }
      out << "\n";
      out.resetColor();
    }
  }
  out << "End trace\n";
  return out;
}

namespace solver_bmc_impl {

bool isCallToVoidFn(const llvm::Instruction &I) {
  if (const CallInst *ci = dyn_cast<const CallInst>(&I))
    if (const Function *fn = ci->getCalledFunction())
      return fn->getReturnType()->isVoidTy();

  return false;
}

void get_model_implicant(const ExprVector &f, solver::Solver::model_ref model,
                         ExprVector &out, ExprMap &active_bool_map) {
  // XXX This is a partial implementation. Specialized to the
  // constraints expected to occur in m_side.

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

} // end namespace solver_bmc_impl

} // namespace seahorn
