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
  typedef enum { mono_bmc, path_bmc} bmc_engine_t;
}


namespace seahorn
{
  using namespace expr;
  
  namespace bmc_impl {
    /// true if I is a call to a void function
    bool isCallToVoidFn (const llvm::Instruction &I);
    /// computes an implicant of f (interpreted as a conjunction) that
    /// contains the given model    
    void get_model_implicant (const ExprVector &f, 
			      ufo::ZModel<ufo::EZ3> &model, ExprVector &out,
			      ExprMap& active_bool_map);
    // out is a minimal unsat core f based on assumptions
    void unsat_core(ufo::ZSolver<ufo::EZ3>& solver, const ExprVector& f, ExprVector& out);
  } // end namespace
  
  class BmcTrace;  
  class BmcEngine 
  {
  protected:
    /// symbolic operational semantics
    SmallStepSymExec& m_sem;
    /// expression factory
    ExprFactory &m_efac;
    
    /// last result
    boost::tribool m_result;
    
    /// cut-point trace
    SmallVector<const CutPoint *, 8> m_cps;
    
    /// symbolic states corresponding to m_cps
    std::vector<SymStore> m_states;
    /// edge-trace corresponding to m_cps
    SmallVector<const CpEdge*, 8> m_edges;
    
    const CutPointGraph *m_cpg;
    const llvm::Function* m_fn;
    
    ufo::ZSolver<ufo::EZ3> m_smt_solver;
    
    /// path-condition for m_cps
    ExprVector m_side;

  public:
    BmcEngine (SmallStepSymExec &sem, ufo::EZ3 &zctx) : 
      m_sem (sem), m_efac (sem.efac ()), m_result (boost::indeterminate),
      m_cpg (nullptr), m_fn (nullptr),
      m_smt_solver (zctx)
    {};
    
    void addCutPoint (const CutPoint &cp);
    
    SmallStepSymExec& sem () {return m_sem;}
    
    ufo::EZ3 &zctx () { return m_smt_solver.getContext (); }
    
    /// constructs the path condition
    virtual void encode (bool assert_formula = true);
    /// checks satisfiability of the path condition
    virtual boost::tribool solve ();
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

    /// get side condition 
    const ExprVector& getFormula() const { return m_side; }

    /// get cut-point trace
    const SmallVector<const CutPoint*, 8>& getCps() const  { return m_cps; }
    
    /// get edges from the cut-point trace
    const SmallVector<const CpEdge*, 8>& getEdges() const { return m_edges; }

    /// get symbolic states corresponding to the cutpoint trace
    std::vector<SymStore>& getStates() { return  m_states; }

    /// get model if side condition evaluated to sat.
    ufo::ZModel<ufo::EZ3> getModel() {
      assert((bool) result());
      return m_smt_solver.getModel();
    }
    
    /// Returns the BMC trace (if available)
    virtual BmcTrace getTrace ();
    
    /// Dump unsat core 
    /// Exposes internal details. Intendent to be used for debugging only
    virtual void unsatCore (ExprVector &out);

  };
  

  class BmcTrace 
  {
    BmcEngine &m_bmc;
    
    ufo::ZModel<ufo::EZ3> m_model;
    
    /// the trace of basic blocks
    SmallVector<const BasicBlock *, 8> m_bbs;
    
    /// a map from an index of a basic block on a trace to the index
    /// of the corresponding cutpoint in BmcEngine
    SmallVector<unsigned, 8> m_cpId;
          
    /// cutpoint id corresponding to the given location
    unsigned cpid (unsigned loc) const {return m_cpId[loc];}
    
    /// true if loc is the first location on a cutpoint edge
    bool isFirstOnEdge (unsigned loc) const
    {return loc == 0 || cpid (loc - 1) !=  cpid (loc);}
    
    
  public:

    BmcTrace (BmcEngine &bmc, ufo::ZModel<ufo::EZ3> &model);
    
    BmcTrace (const BmcTrace &other) :
      m_bmc (other.m_bmc), m_model (other.m_model),
      m_bbs (other.m_bbs), m_cpId (other.m_cpId) {}
    
    /// underlying BMC engine
    BmcEngine &engine () { return m_bmc; }
    /// The number of basic blocks in the trace 
    unsigned size () const {return m_bbs.size ();}
    
    /// The basic block at a given location 
    const llvm::BasicBlock* bb (unsigned loc) const {return m_bbs [loc];}
    
    /// The value of the instruction at the given location 
    Expr symb (unsigned loc, const llvm::Value &inst);
    Expr eval (unsigned loc, const llvm::Value &inst, bool complete=false);
    Expr eval (unsigned loc, Expr v, bool complete=false);
    template <typename Out> Out &print (Out &out);
  };
}

#endif
