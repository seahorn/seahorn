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
    
    ufo::ZSolver<ufo::EZ3> m_smt;
    
    ExprVector m_side;
    SmallVector<SymStore, 8> m_states;
    SmallVector<const CpEdge*, 9> m_edges;
    
  protected:
    void encode ();
    
  public:
    BmcEngine (SmallStepSymExec &sem, ufo::EZ3 zctx) : 
      m_sem (sem), m_efac (sem.efac ()), m_result (boost::indeterminate),
      m_cpg (nullptr), m_fn (nullptr),
      m_smt (zctx)
    {};
    
    void addCutPoint (const CutPoint &cp);
    
    boost::tribool solve ();
    
    boost::tribool result () { return m_result; }
    ExprFactory &efac () { return m_efac; }
    void reset ();
    
    
    /** Returns a trace (if available) */
    BmcTrace getTrace ();
    
  };
  

  class BmcTrace 
  {
    BmcEngine &m_bmc;
    
    public:
    BmcTrace (BmcEngine &bmc) : m_bmc (bmc) {}
    
    /** number of basic blocks in the trace */
    unsigned size ();

    /** return basic block at a given location */
    const llvm::BasicBlock* bb (unsigned loc);
    
    /** The value of the instruction at the given location */
    Expr eval (unsigned loc, const llvm::Instruction &inst);
    
  };
}

#endif
