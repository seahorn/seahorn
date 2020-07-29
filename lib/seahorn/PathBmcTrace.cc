#pragma once

#include "seahorn/config.h"

#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"

#include "seahorn/Bmc.hh"
#include "seahorn/Expr/Smt/Model.hh"
#include "seahorn/PathBmc.hh"
#include "seahorn/PathBmcUtil.hh"
#include "seahorn/Support/SeaDebug.h"

namespace seahorn {

using namespace llvm;

void PathBmcTrace::getModelImplicant(const ExprVector &f) {
  // XXX This is a partial implementation. Specialized to the
  // constraints expected to occur in m_side.
  Expr bool_lit = nullptr;
  for (auto v : f) {
    // -- break IMPL into an OR
    // -- OR into a single disjunct
    // -- single disjunct into an AND
    if (isOpX<IMPL>(v)) {
      assert(v->arity() == 2);
      Expr v0 = m_model->eval(v->arg(0), false);
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
        if (isOpX<TRUE>(m_model->eval(v->arg(i), false))) {
          v = v->arg(i);
          break;
        }
    }
    if (isOpX<AND>(v)) {
      for (unsigned i = 0; i < v->arity(); ++i) {
        m_trace.push_back(v->arg(i));
        if (bool_lit)
          m_bool_map[v->arg(i)] = bool_lit;
      }
    } else {
      m_trace.push_back(v);
      if (bool_lit)
        m_bool_map[v] = bool_lit;
    }
  }
}

PathBmcTrace::PathBmcTrace(PathBmcEngine &bmc, solver::Solver::model_ref model)
    : m_bmc(bmc), m_model(model) {

  // construct an implicant of the precise condition
  const ExprVector &encoding = m_bmc.getPreciseEncoding();

  m_trace.reserve(encoding.size());
  ExprMap bool_map /*unused*/;
  getModelImplicant(encoding);
  boost::container::flat_set<Expr> implicant(m_trace.begin(), m_trace.end());

  // construct the trace from the implicant

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

Expr PathBmcTrace::symb(unsigned loc, const Value &val) {
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

Expr PathBmcTrace::eval(unsigned loc, const Value &val, bool complete) {
  Expr v = symb(loc, val);
  if (v)
    v = m_model->eval(v, complete);
  return v;
}

Expr PathBmcTrace::eval(unsigned loc, Expr u, bool complete) {

  unsigned stateidx = cpid(loc);
  stateidx++;
  // -- out of bounds, no value in the model
  if (stateidx >= m_bmc.getStates().size())
    return Expr();

  SymStore &store = m_bmc.getStates()[stateidx];

  Expr v;
  if (path_bmc::expr_utils::isEdge(u)) {
    // HACK: s.eval does not traverse function declarations
    auto t = path_bmc::expr_utils::getEdge(u);
    if (store.isDefined(t.first) && store.isDefined(t.second)) {
      v = path_bmc::expr_utils::mkEdge(store.eval(t.first),
                                       store.eval(t.second));
    }
  } else {
    v = store.eval(u);
  }

  assert(v);
  return m_model->eval(v, complete);
}

void PathBmcTrace::print(raw_ostream &out) {
  out << "Begin trace \n";
  for (unsigned loc = 0; loc < size(); ++loc) {
    const BasicBlock &BB = *bb(loc);
    out << BB.getName() << ": \n";

    for (auto &I : BB) {
      if (const DbgValueInst *dvi = dyn_cast<DbgValueInst>(&I)) {
        if (dvi->getValue() && dvi->getVariable()) {
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
        }
      }

      if (print_inst) {
        out << I << "\n";
      }

      Expr v = eval(loc, I);
      if (!v)
        continue;

      out.changeColor(raw_ostream::RED);
      out << "  %" << I.getName() << " " << *v;
      const DebugLoc &dloc = I.getDebugLoc();
      if (dloc) {
        out.changeColor(raw_ostream::BLACK);
        out << " [" << (*dloc).getFilename() << ":" << dloc.getLine() << "]";
      }
      out << "\n";
      out.resetColor();
    }
  }
  out << "End trace\n";
}

} // end namespace seahorn
