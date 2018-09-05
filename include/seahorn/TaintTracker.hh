///
/// class TaintTracker
///

#ifndef _TAINT_TRACKER__H_
#define _TAINT_TRACKER__H_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "ufo/Expr.hpp"
#include "boost/range.hpp"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornToSMT.hh"
#include "seahorn/HornCtrlDep.hh"
#include <vector>
#include <sstream>

#include "ufo/Smt/EZ3.hh"
#include "ufo/Smt/Z3n.hpp"

namespace seahorn
{

  ///
  /// class TaintTracker instruments horn clauses by creating additional taint variable for 
  /// each program variable, and insert clauses that compute taint propagation.
  ///
  class TaintTracker
  {
  private:
    HornClauseDB &db;
    HornClauseDBCallGraph &cg;
    HornCtrlDep cdg;
    expr::Expr false_expr;
    // HornClauseDB *db_ptr; ///< temporary storage of the DB
    expr::ExprMap taint_var_map; ///< storing the mapping from program variable to its taint variable 
    HornToSMT::rule_map_type taint_rule_map; ///< mapping from Predicate to Taint Assignments 
    expr::ExprMap branch_cond_map; ///< mapping from branch Predicate to branch Condition 
    std::map<expr::ExprPair, bool> branch_dir_map;
    


    template <class Range>
    expr::Expr mk_or_expr(Range& r)
    {
      size_t size = boost::distance(r);
      if (size == 0) return false_expr;
      else if (size == 1) return *boost::begin(r);
      else return expr::mknary<expr::OR>(r);
    }

    /// Access the corresponding taint variable for \p var
    ///
    expr::Expr get_taint_var(expr::Expr var);
    void get_taint_list(expr::Expr e, expr::ExprVector& v);
    expr::Expr get_ite_taint(expr::Expr ite);
    expr::Expr get_control_taint(expr::Expr rel);
    expr::Expr get_br_cond(expr::Expr rel, HornToSMT::rule_map_type &rules);
    /// Create and solve the query on the expresion \p e
    /// The result indicates if the expression is tainted (dynamically), which is
    /// used by the self-composer (InflowChecker) to decide whether or nor to duplicate
    /// a certaint part of the horn program.
    // boost::tribool queryTaint(HornClauseDB &db, expr::Expr e);
  public:
    
    TaintTracker (HornClauseDB &hcdb, HornClauseDBCallGraph& hccg)
    : db(hcdb), cg(hccg), cdg(db, cg), false_expr(mk<FALSE>(db.getExprFactory())){}

    /// Apply taint analysis on clause DB.
    /// This function creates taint variables and taint propagation clauses
    /// for the non-recursive part of the horn program, after removing loops
    /// and before adding loop bodies (unrolling).
    ///
    /// \param db should be loop free (after HornUnroll::cutLoops)
    void applyTaint(HornToSMT &smt);

    /// Apply taint analysis on clause DB.
    /// Here only rules in \p new_rules are instrumented, assuming \p db
    /// has already been processed by the first applyTaint()
    ///
    /// \param db clause DB right after one unroll
    /// \param new_rules contain rules added by the unroller, the new loop body
    // void applyTaint(HornClauseDB &db, HornCtrlDep &cdg, std::vector<HornRule> new_rules);
    void toSMT(ufo::ZSolver<ufo::EZ3> &solver);
    
    template<class T>
    T& write(T& stream)
    {
      std::ostringstream oss;
      for (auto& p: taint_rule_map)
      {
        Expr caller = p.first.first, callee = p.first.second;
        oss<<"Taint for rule "<<*(caller->left())<<" => "<<*(callee->left())<<" is "<<*(p.second)<<"\n";
      }
      
      stream<<oss.str();
      stream.flush();
      return stream;
    }
  };
}


#endif /* _TAINT_TRACKER__H_ */
