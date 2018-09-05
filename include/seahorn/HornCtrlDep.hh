///
/// class HornCtrlDep
///

#ifndef _HORN_CTRLDEP__H_
#define _HORN_CTRLDEP__H_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "ufo/Expr.hpp"
#include "seahorn/HornClauseDB.hh"
#include <memory>
#include <map>
#include <vector>
#include <algorithm>

namespace seahorn
{

using namespace llvm;
  
  ///
  /// class HornDomTree
  /// Worklist algorithm to construct the Dominator Tree
  class HornDomTree
  {
  private:
    HornClauseDB& db; 
    HornClauseDBCallGraph &cg;
    bool reverse;
    expr::Expr false_expr;
    expr::ExprMap idom_map;
    std::map<expr::Expr, expr::ExprSet> dom_map;

    expr::ExprSet empty_set;

  public:
    HornDomTree(HornClauseDB& hcdb, HornClauseDBCallGraph &hccg, bool reverse = false);
    expr::Expr immDom(expr::Expr fdecl);

    const expr::ExprSet& allDom(expr::Expr fdecl);
    ~HornDomTree() {}
  };
  ///
  ///
  class HornCtrlDep
  {

  private:
    HornClauseDB& db;     ///< db storing all the horn rules 
    HornClauseDBCallGraph& cg;

    HornDomTree pdt; ///< post (immediate) dominator tree

    expr::ExprMap cd_map;

    expr::ExprSet empty_set;
  public:
    HornCtrlDep(HornClauseDB& hcdb, HornClauseDBCallGraph& hccg);

    expr::Expr ctrlDep(expr::Expr fdecl);
    ~HornCtrlDep() {}
  };
}


#endif /* _HORN_CTRLDEPGRAPH__H_ */
