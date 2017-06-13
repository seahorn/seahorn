#ifndef __BMC__HH_
#define  __BMC__HH_

#include "llvm/IR/Function.h"

#include "boost/logic/tribool.hpp"

#include "ufo/Expr.hpp"
#include "ufo/Smt/EZ3.hh"

#include "seahorn/Analysis/CutPointGraph.hh"
#include "seahorn/SymExec.hh"

#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DebugInfo.h"

#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"

namespace seahorn
{
  using namespace expr;
  class BmcTrace;
  
  class BmcEngine 
  {
    /// symbolic operational semantics
    SmallStepSymExec& m_sem;
    /// expression factorysdfasdf
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
    
    /// Dump unsat core 
    /// Exposes internal details. Intendent to be used for debugging only
    void unsatCore (ExprVector &out);

    friend class BmcTrace;
    
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
    
    
    BmcTrace (BmcEngine &bmc, ufo::ZModel<ufo::EZ3> &model);

    
    /// cutpoint id corresponding to the given location
    unsigned cpid (unsigned loc) const {return m_cpId[loc];}
    
    /// true if loc is the first location on a cutpoint edge
    bool isFirstOnEdge (unsigned loc) const
    {return loc == 0 || cpid (loc - 1) !=  cpid (loc);}
    
    
  public:
    
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
    friend class BmcEngine;
  };
  
  template <typename Out> 
  Out &BmcTrace::print (Out &out) 
  {
    using namespace llvm;
    
    for (unsigned loc = 0; loc < size (); ++loc)
    {
      const BasicBlock &BB = *bb(loc);
      out << BB.getName () << ": \n";
      
      for (auto &I : BB)
      {
        if (const DbgValueInst *dvi = dyn_cast<DbgValueInst> (&I))
        {
          if (dvi->getValue () && dvi->getVariable ())
          {
            DILocalVariable *var = dvi->getVariable ();
            out << "  " << var->getName () << " = ";
            if (dvi->getValue ()->hasName ())
              out << dvi->getValue ()->getName ();
            else
              out << *dvi->getValue ();
            out << "\n";
          }
          continue;
        }

        if (const CallInst *ci = dyn_cast<CallInst> (&I))
        {
          Function *f = ci->getCalledFunction ();
          if (f && f->getName ().equals ("seahorn.fn.enter"))
          {
	    if (ci->getDebugLoc ()) {
	      if (DISubprogram *fnScope = getDISubprogram (ci->getDebugLoc ().getScope ())) 
		out << "enter: " << fnScope->getDisplayName () << "\n";
	    }
            continue;
          }
          else if (f && f->getName ().equals ("shadow.mem.init"))
          {
            int64_t id = shadow_dsa::getShadowId (ci);
            assert (id >= 0);
            Expr memStart = m_bmc.sem().memStart (id);
            Expr u = eval (loc, memStart);
            if (u) out << "  " << *memStart << " " << *u << "\n";
            Expr memEnd = m_bmc.sem().memEnd (id);
            u = eval (loc, memEnd);
            if (u) out << "  " << *memEnd << " " << *u << "\n";
          }
        }
               
               
        Expr v = eval (loc, I);
        if (!v) continue;
        out << "  %" << I.getName () << " " << *v;
        
        const DebugLoc &dloc = I.getDebugLoc ();
        if (dloc)
        {
          out << "\t[" << (*dloc).getFilename () << ":"
	               << dloc.getLine () << "]";
        }
        out << "\n";
      }        
    }
    return out;
  }
  
  
}

#endif
