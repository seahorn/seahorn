#include "seahorn/Bmc.hh"
#include "seahorn/UfoSymExec.hh"

#include "boost/container/flat_set.hpp"

namespace seahorn
{
  /// computes an implicant of f (interpreted as a conjunction) that
  /// contains the given model
  static void get_model_implicant (const ExprVector &f, 
                                   ufo::ZModel<ufo::EZ3> &model, ExprVector &out);
  /// true if I is a call to a void function
  static bool isCallToVoidFn (const llvm::Instruction &I);
  
    
  void BmcEngine::addCutPoint (const CutPoint &cp)
  {
    if (m_cps.empty ())
    {
      m_cpg = &cp.parent ();
      m_fn = cp.bb ().getParent ();
    }
  
    assert (m_cpg == &cp.parent ());
    m_cps.push_back (&cp);
  }

  boost::tribool BmcEngine::solve ()
  {
    encode ();
    m_result =  m_smt_solver.solve ();
    return m_result;
  }

  void BmcEngine::encode ()
  {
    
    // -- only run the encoding once
    if (!m_side.empty ()) return;
    
    assert (m_cpg);
    assert (m_fn);
    UfoLargeSymExec sexec (m_sem);
    m_states.push_back (SymStore (m_efac));
    
    const CutPoint *prev = nullptr;
    for (const CutPoint *cp : m_cps)
    {
      if (prev)
      {
        const CpEdge *edg = m_cpg->getEdge (*prev, *cp);
        assert (edg);
        m_edges.push_back (edg);
      
        m_states.push_back (m_states.back ());
        SymStore &s = m_states.back ();
        sexec.execCpEdg (s, *edg, m_side);
      }
      prev = cp;
    }
    
    for (Expr v : m_side) m_smt_solver.assertExpr (v);
    
  }

  void BmcEngine::reset ()
  {
    m_cps.clear ();
    m_cpg = nullptr;
    m_fn = nullptr;
    m_smt_solver.reset ();

    m_side.clear ();
    m_states.clear ();
    m_edges.clear ();
  }
  
  
  void BmcEngine::unsatCore (ExprVector &out)
  {
    // -- re-assert the path-condition with assumptions
    m_smt_solver.reset ();
    ExprVector assumptions;
    assumptions.reserve (m_side.size ());
    for (Expr v : m_side)
    {
      Expr a = bind::boolConst (mk<ASM> (v));
      assumptions.push_back (a);
      m_smt_solver.assertExpr (mk<IMPL> (a, v));
    }
    
    ExprVector core;
    m_smt_solver.push ();
    boost::tribool res = m_smt_solver.solveAssuming (assumptions);
    if (!res) m_smt_solver.unsatCore (std::back_inserter (core));
    m_smt_solver.pop ();
    if (res) return;

    
    // simplify core
    while (core.size () < assumptions.size ())
    {
      assumptions.assign (core.begin (), core.end ());
      core.clear ();
      m_smt_solver.push ();
      res = m_smt_solver.solveAssuming (assumptions);
      assert (!res ? 1 : 0);
      m_smt_solver.unsatCore (std::back_inserter (core));
      m_smt_solver.pop ();
    }    
    
    // minimize simplified core
    for (unsigned i = 0; i < core.size ();)
    {
      Expr saved = core [i];
      core [i] = core.back ();
      res = m_smt_solver.solveAssuming 
        (boost::make_iterator_range (core.begin (), core.end () - 1));
      if (res) core [i++] = saved;
      else if (!res)
        core.pop_back ();
      else assert (0);
    }
    
    // unwrap the core from ASM to corresponding expressions
    for (Expr c : core)
      out.push_back (bind::fname (bind::fname (c))->arg (0));
  }
  
  BmcTrace BmcEngine::getTrace ()
  {
    assert ((bool)m_result);
    auto model = m_smt_solver.getModel ();
    return BmcTrace (*this, model);
  }
  
  BmcTrace::BmcTrace (BmcEngine &bmc, ufo::ZModel<ufo::EZ3> &model) :
    m_bmc (bmc), m_model(m_bmc.m_smt_solver.getContext ())
  {
    assert ((bool)bmc.result ());
    
    m_model = bmc.m_smt_solver.getModel ();
    

    // construct an implicant of the side condition
    ExprVector trace;
    trace.reserve (m_bmc.m_side.size ());
    get_model_implicant (m_bmc.m_side, m_model, trace);
    boost::container::flat_set<Expr> implicant (trace.begin (), trace.end ());
    
    
    // construct the trace
    
    // -- reference to the first state
    auto st = m_bmc.m_states.begin ();
    // -- reference to the fist cutpoint in the trace
    unsigned id = 0;
    for (const CpEdge *edg : m_bmc.m_edges)
    {
      LOG("cex",
          errs () << "";);
      
      assert (&(edg->source ()) == m_bmc.m_cps [id]);
      assert (&(edg->target ()) == m_bmc.m_cps [id+1]);
      
      SymStore &s = *(++st);
      for (auto it = edg->begin (), end = edg->end (); it != end; ++it)
      {
        const BasicBlock &BB = *it;
        
        if (it != edg->begin () && 
            implicant.count (s.eval (m_bmc.m_sem.symb (BB))) <= 0) 
          continue;
        
        m_bbs.push_back (&BB);
        m_cpId.push_back (id);
      }
      // -- next basic block corresponds to the next cutpoint
      id++;
    }
    
    // -- last block on the edge
    if (!m_bmc.m_edges.empty ())
    {
      m_bbs.push_back (&m_bmc.m_edges.back ()->target ().bb ());
      m_cpId.push_back (id);
    }
    else
    {
      assert (m_bmc.m_cps.size () == 1);
      // special case of trivial counterexample. The counterexample is
      // completely contained within the first cutpoint
      m_bbs.push_back (&m_bmc.m_cps [0]->bb ());
      m_cpId.push_back (0);
    }
  }
  
  Expr BmcTrace::symb (unsigned loc, const llvm::Value &val)
  {
    // assert (cast<Instruction>(&val)->getParent () == bb(loc));
    
    if (!m_bmc.m_sem.isTracked (val)) return Expr ();
    if (isa<Instruction> (val) && isCallToVoidFn (cast<Instruction>(val))) return Expr ();
    Expr u = m_bmc.m_sem.symb (val);
    
    unsigned stateidx = cpid(loc);
    // -- all registers except for PHI nodes at the entry to an edge
    // -- get their value at the end of the edge
    if (! (isa<PHINode> (val) && isFirstOnEdge (loc)) ) stateidx++;
    // -- out of bounds, no value in the model
    if (stateidx >= m_bmc.m_states.size ()) return Expr ();
    
    SymStore &store = m_bmc.m_states[stateidx];
    return store.eval (u);
  }
  
  Expr BmcTrace::eval (unsigned loc,
                       const llvm::Value &val,
                       bool complete) 
  {
    Expr v = symb (loc, val);
    if (v) v = m_model.eval (v, complete);
    return v;
  }
  
  Expr BmcTrace::eval (unsigned loc,
                       Expr u, 
                       bool complete) 
  {
    
    unsigned stateidx = cpid(loc);
    stateidx++;
    // -- out of bounds, no value in the model
    if (stateidx >= m_bmc.m_states.size ()) return Expr ();
    
    SymStore &store = m_bmc.m_states[stateidx];
    Expr v = store.eval (u);
    return m_model.eval (v, complete);
  }

  
  static bool isCallToVoidFn (const llvm::Instruction &I)
  {
    if (const CallInst *ci = dyn_cast<const CallInst> (&I))
      if (const Function *fn = ci->getCalledFunction ())
        return fn->getReturnType ()->isVoidTy ();
    
    return false;
  }


  static void get_model_implicant (const ExprVector &f, 
                                   ufo::ZModel<ufo::EZ3> &model, ExprVector &out)
  {
    // XXX This is a partial implementation. Specialized to the
    // constraints expected to occur in m_side.
    
    for (auto v : f)
    {
      // -- break IMPL into an OR
      // -- OR into a single disjunct
      // -- single disjunct into an AND
      if (isOpX<IMPL> (v))
      {
        assert (v->arity () == 2);
        Expr a0 = model (v->arg (0));
        if (isOpX<FALSE> (a0)) continue;
        else if (isOpX<TRUE> (a0))
          v = mknary<OR> (mk<FALSE> (a0->efac ()), 
                          ++(v->args_begin ()), v->args_end ());
        else
          continue;
      }
      
      if (isOpX<OR> (v))
      {
        for (unsigned i = 0; i < v->arity (); ++i)
          if (isOpX<TRUE> (model (v->arg (i))))
          {
            v = v->arg (i);
            break;
          }
      }
        
      if (isOpX<AND> (v)) 
      {
        for (unsigned i = 0; i < v->arity (); ++i)
          out.push_back (v->arg (i));
      }
      else out.push_back (v);
    }      
    
  }

}
