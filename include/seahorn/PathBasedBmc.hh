#pragma once

#include "seahorn/config.h"
#include "seahorn/Bmc.hh"
#include "seahorn/LiveSymbols.hh"

#include "boost/unordered_set.hpp"

#ifdef HAVE_CRAB_LLVM
#include "crab_llvm/CrabLlvm.hh"
#endif 

namespace llvm {
  class TargetLibraryInfo;
}

/*
  Rather than building one monolithic precise encoding of the program
  and check its satisfiability, this BMC engine enumerates
  symbolically all paths using an abstraction of the precise encoding
  of the program. This enumeration continues until a path is
  satisfiable or no more paths exist.
 */
namespace seahorn
{  
  class PathBasedBmcEngine: public BmcEngine {
  public:
    PathBasedBmcEngine (SmallStepSymExec &sem, ufo::EZ3 &zctx,
			const llvm::TargetLibraryInfo& tli);

    ~PathBasedBmcEngine();
        
    /// Enumerate paths until a path is satisfiable or there is no
    /// more paths.
    virtual boost::tribool solve () override;

    /// Returns the BMC trace (if available)
    virtual BmcTrace getTrace () override;

    /// constructs the path condition (NOT implemented)
    virtual void encode () override;
    
    /// Dump unsat core  (NOT implemented)
    virtual void unsatCore (ExprVector &out) override;
    
  private:
    
    ufo::ZSolver<ufo::EZ3> m_aux_smt_solver;        
    const llvm::TargetLibraryInfo& m_tli;

    // Boolean literals that active the implicant: used to produce
    // blocking clauses for the Boolean abstraction.
    ExprVector m_active_bool_lits;
    // model of a path formula
    ufo::ZModel<ufo::EZ3> m_model;
    // live symbols
    LiveSymbols* m_ls;
    // Temporary sanity check: bookeeping of all generated blocking
    // clauses.
    boost::unordered_set<Expr> m_blocking_clauses;

    // Check feasibility of a path induced by model using SMT solver.
    // Return true (sat), false (unsat), or indeterminate (inconclusive).
    // If unsat then it produces a blocking clause.
    typedef DenseMap<const BasicBlock*, ExprVector> invariants_map_t;    
    boost::tribool path_encoding_and_solve_with_smt(ufo::ZModel<ufo::EZ3> &model,
						    const invariants_map_t& invariants,
						    const invariants_map_t& path_constraints);
    
    #ifdef HAVE_CRAB_LLVM
    // Check feasibility of a path induced by trace using abstract
    // interpretation.
    // Return true (sat) or false (unsat). If unsat then it produces a
    // blocking clause.
    bool path_encoding_and_solve_with_ai(BmcTrace &trace, 
					 const crab_llvm::IntraCrabLlvm& crab,
					 invariants_map_t& path_constraints);
    #endif 

    // Return false if a blocking clause has been generated twice.
    bool add_blocking_clauses();
  };
}
