#pragma once
#include "seahorn/Bmc.hh"

namespace seahorn {
namespace bmc_impl {
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
} // namespace bmc_impl

template <class Engine, class Model>
void BmcTrace<Engine, Model>::constructTrace() {
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

template <class Engine, class Model>
Expr BmcTrace<Engine, Model>::symb(unsigned loc, const llvm::Value &val) {
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

template <class Engine, class Model>
Expr BmcTrace<Engine, Model>::eval(unsigned loc, const llvm::Value &inst,
                                   bool complete) {
  if (auto *constInt = dyn_cast<ConstantInt>(&inst)) {
    expr::mpz_class constIntVal = toMpz(constInt);
    return expr::mkTerm<expr::mpz_class>(constIntVal, engine().efac());
  }
  Expr v = symb(loc, inst);
  if (v)
    v = m_model->eval(v, complete);
  return v;
}

template <class Engine, class Model>
Expr BmcTrace<Engine, Model>::eval(unsigned loc, Expr u, bool complete) {

  unsigned stateidx = cpid(loc);
  stateidx++;
  // -- out of bounds, no value in the model
  if (stateidx >= m_bmc.getStates().size())
    return Expr();

  SymStore &store = m_bmc.getStates()[stateidx];
  Expr v = store.eval(u);
  return m_model->eval(v, complete);
}

template <class Engine, class Model>
template <typename Out>
Out &BmcTrace<Engine, Model>::print(Out &out) {
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
} // namespace seahorn
