#include "seahorn/Bmc.hh"
#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"
#include "seahorn/UfoOpSem.hh"

#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/Support/CommandLine.h"

#include "boost/container/flat_set.hpp"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/HexDump.hh"
#include "seahorn/Support/SeaDebug.h"

static llvm::cl::opt<bool>
    DumpHex("horn-bmc-hexdump",
            llvm::cl::desc("Dump memory state using hexdump"), cl::init(false));
static llvm::cl::opt<std::string>
    BmcSmtTactic("horn-bmc-tactic", llvm::cl::desc("Z3 tactic to use for BMC"),
                 cl::init("default"));
static llvm::cl::opt<std::string>
    BmcSmtLogic("horn-bmc-logic", llvm::cl::desc("SMT-LIB logic to pass to Z3"),
                cl::init("ALL"));

namespace seahorn {
BmcEngine::BmcEngine(OperationalSemantics &sem, EZ3 &zctx)
    : m_sem(sem), m_efac(sem.efac()), m_result(boost::indeterminate),
      m_cpg(nullptr), m_fn(nullptr), m_smt_solver(zctx, BmcSmtLogic.c_str()),
      m_ctxState(m_efac) {

  z3n_set_param(":model.compact", false);
  if (BmcSmtTactic != "default")
    z3n_set_param(":tactic.default_tactic", BmcSmtTactic.c_str());
}

void BmcEngine::addCutPoint(const CutPoint &cp) {
  if (m_cps.empty()) {
    m_cpg = &cp.parent();
    m_fn = cp.bb().getParent();
  }

  assert(m_cpg == &cp.parent());
  m_cps.push_back(&cp);
}

boost::tribool BmcEngine::solve() {
  encode();
  m_result = m_smt_solver.solve();
  return m_result;
}

void BmcEngine::encode(bool assert_formula) {

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
      m_smt_solver.assertExpr(v);
  }
}

void BmcEngine::reset() {
  m_cps.clear();
  m_cpg = nullptr;
  m_fn = nullptr;
  m_smt_solver.reset();

  m_side.clear();
  m_states.clear();
  m_edges.clear();
}

void BmcEngine::unsatCore(ExprVector &out) {
  const bool simplify = true;
  bmc_impl::unsat_core(m_smt_solver, m_side, simplify, out);
}

/// output current path condition in SMT-LIB2 format
raw_ostream &BmcEngine::toSmtLib(raw_ostream &out) {
  if (BmcSmtLogic != "ALL")
    out << "(set-logic " << BmcSmtLogic << ")\n";
  encode();
  return m_smt_solver.toSmtLib(out);
}

BmcTrace BmcEngine::getTrace() {
  assert((bool)m_result);
  auto model = m_smt_solver.getModel();
  return BmcTrace(*this, model);
}

BmcTrace::BmcTrace(BmcEngine &bmc, ZModel<EZ3> &model)
    : m_bmc(bmc), m_model(model /*m_bmc.zctx()*/) {
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

Expr BmcTrace::symb(unsigned loc, const llvm::Value &val) {
  // assert (cast<Instruction>(&val)->getParent () == bb(loc));

  if (!m_bmc.sem().isTracked(val))
    return Expr();
  if (isa<Instruction>(val) && bmc_impl::isCallToVoidFn(cast<Instruction>(val)))
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

Expr BmcTrace::eval(unsigned loc, const llvm::Value &val, bool complete) {
  Expr v = symb(loc, val);
  if (v)
    v = m_model.eval(v, complete);
  return v;
}

Expr BmcTrace::eval(unsigned loc, Expr u, bool complete) {

  unsigned stateidx = cpid(loc);
  stateidx++;
  // -- out of bounds, no value in the model
  if (stateidx >= m_bmc.getStates().size())
    return Expr();

  SymStore &store = m_bmc.getStates()[stateidx];
  Expr v = store.eval(u);
  return m_model.eval(v, complete);
}

// template <typename Out> Out &BmcTrace::print (Out &out)
template <> raw_ostream &BmcTrace::print(raw_ostream &out) {
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

namespace bmc_impl {

bool isCallToVoidFn(const llvm::Instruction &I) {
  if (const CallInst *ci = dyn_cast<const CallInst>(&I))
    if (const Function *fn = ci->getCalledFunction())
      return fn->getReturnType()->isVoidTy();

  return false;
}

void get_model_implicant(const ExprVector &f, ZModel<EZ3> &model,
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
      Expr v0 = model(v->arg(0));
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
        if (isOpX<TRUE>(model(v->arg(i)))) {
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

void unsat_core(ZSolver<EZ3> &solver, const ExprVector &f, bool simplify,
                ExprVector &out) {
  solver.reset();
  ExprVector assumptions;
  assumptions.reserve(f.size());
  for (Expr v : f) {
    Expr a = bind::boolConst(mk<ASM>(v));
    assumptions.push_back(a);
    solver.assertExpr(mk<IMPL>(a, v));
  }

  ExprVector core;
  solver.push();
  boost::tribool res = solver.solveAssuming(assumptions);
  if (!res)
    solver.unsatCore(std::back_inserter(core));
  solver.pop();
  if (res)
    return;

  if (simplify) {
    // simplify core
    while (core.size() < assumptions.size()) {
      assumptions.assign(core.begin(), core.end());
      core.clear();
      solver.push();
      res = solver.solveAssuming(assumptions);
      assert(!res ? 1 : 0);
      solver.unsatCore(std::back_inserter(core));
      solver.pop();
    }

    // minimize simplified core
    for (unsigned i = 0; i < core.size();) {
      Expr saved = core[i];
      core[i] = core.back();
      res = solver.solveAssuming(
          boost::make_iterator_range(core.begin(), core.end() - 1));
      if (res)
        core[i++] = saved;
      else if (!res)
        core.pop_back();
      else
        assert(0);
    }
  }

  // unwrap the core from ASM to corresponding expressions
  for (Expr c : core)
    out.push_back(bind::fname(bind::fname(c))->arg(0));
}

} // end namespace bmc_impl

} // namespace seahorn
