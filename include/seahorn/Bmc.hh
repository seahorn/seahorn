#ifndef __BMC__HH_
#define  __BMC__HH_

#include "llvm/IR/Function.h"

#include "boost/logic/tribool.hpp"

#include "ufo/Expr.hpp"
#include "ufo/Smt/EZ3.hh"

#include "seahorn/Analysis/CutPointGraph.hh"
#include "seahorn/SymExec.hh"

namespace seahorn
{
  using namespace expr;
  class BmcTrace;
  
  class BmcEngine 
  {
    /// symbolic operational semantics
    SmallStepSymExec& m_sem;
    /// expression factory
    ExprFactory &m_efac;
    
    /// last result
    boost::tribool m_result;
    
    /// cut-point trace
    SmallVector<const CutPoint *, 8> m_cps;
    
    const CutPointGraph *m_cpg;
    const llvm::Function* m_fn;
    
    ufo::ZSolver<ufo::EZ3> m_smt_solver;
    
    /// path-condition for m_cps
    ExprVector m_side;
    /// symbolic states corresponding to m_cps
    SmallVector<SymStore, 8> m_states;
    /// edge-trace corresponding to m_cps
    SmallVector<const CpEdge*, 8> m_edges;
    
    
  public:
    BmcEngine (SmallStepSymExec &sem, ufo::EZ3 &zctx) : 
      m_sem (sem), m_efac (sem.efac ()), m_result (boost::indeterminate),
      m_cpg (nullptr), m_fn (nullptr),
      m_smt_solver (zctx)
    {};
    
    void addCutPoint (const CutPoint &cp);
    
    /// constructs the path condition
    void encode ();
    /// checks satisfiability of the path condition
    boost::tribool solve ();
    /// returns the latest result from solve() 
    boost::tribool result () { return m_result; }
    
    
    /// output current path condition in SMT-LIB2 format
    template<typename OutputStream>
    OutputStream &toSmtLib (OutputStream &out) 
    { encode (); return m_smt_solver.toSmtLib (out); }
    
    /// access to expression factory
    ExprFactory &efac () { return m_efac; }
    
    /// reset the engine
    void reset ();
    
    
    /// Returns the BMC trace (if available)
    BmcTrace getTrace ();
    
  };
  

  class BmcTrace 
  {
    BmcEngine &m_bmc;
    
    BmcTrace (BmcEngine &bmc) : m_bmc (bmc) {}
    
    public:
    
    /// The number of basic blocks in the trace 
    unsigned size ();

    /// The basic block at a given location 
    const llvm::BasicBlock* bb (unsigned loc);
    
    /// The value of the instruction at the given location 
    Expr eval (unsigned loc, const llvm::Instruction &inst);
    
    friend class BmcEngine;
  };
}

#endif
