#pragma once

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprOpBind.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"
#include "seahorn/Expr/ExprVisitor.hh"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornModelConverter.hh"
#include "seahorn/Support/SeaDebug.h"

using namespace expr;
using namespace expr::op;

namespace seahorn {

// Rewrites a finite map operation whose arguments are already rewritten
struct FiniteMapTransRewriter : public std::unary_function<Expr, Expr> {
  // put Expr as a friend class have access to expr->args()??

  // HornClauseDB &m_db;
  // ExprSet m_vars; // expressions that are vars, this needs to be updated if new
  //                 // variables are introduced while rewriting
  ExprFactory &m_efac;
  ExprMap &m_mkeys;
  // ExprMap &m_mapvars_keys;
  // ExprMap &m_mapvars_expr;
  Expr m_lmd_keys; // make this an ExprVector for predicate calls?

  FiniteMapTransRewriter(ExprFactory &efac, ExprMap &mkeys)
    : m_efac(efac), m_mkeys(mkeys) {
    m_lmd_keys = nullptr;
  };

  Expr operator()(Expr exp) {
    Expr lmd_map;
    if (isOpX<CONST_FINITE_MAP>(exp)) {
      ExprVector keys(exp->args_begin(), exp->args_end());
      m_lmd_keys = finite_map::make_lambda_map_keys(keys, m_efac);
      lmd_map = finite_map::empty_map_lambda(m_efac);
    } else if (isOpX<GET>(exp)) {
      assert(m_lmd_keys);
      lmd_map =
          finite_map::get_map_lambda(exp->left(), m_lmd_keys, exp->right());
    } else if (isOpX<SET>(exp)) {
      assert(m_lmd_keys);
      ExprVector args(exp->args_begin(), exp->args_end());
      Expr value = args[2];
      lmd_map = finite_map::set_map_lambda(exp->left(), m_lmd_keys,
                                           exp->right(), value, m_efac);
    } else if (isOpX<EQ>(exp)) {
      // this will be asked to the HCDB
      // if (isMapVar(exp->right())) // if it is of type map
      return exp;
    } else { // do nothing
      return exp;
    }
    errs() << "Rewritten: " << *exp << "\n    " << *lmd_map << "\n";
    return lmd_map;
  }

};
struct FiniteMapTransVisitor : public std::unary_function<Expr, VisitAction> {

  ExprMap map_keys;
  ExprFactory &m_efac;
  std::shared_ptr<FiniteMapTransRewriter> m_rw;

  FiniteMapTransVisitor(ExprFactory &efac)
    : m_efac(efac){
    m_rw = std::make_shared<FiniteMapTransRewriter>(m_efac, map_keys);
  }
  VisitAction operator()(Expr exp) {
    if (isOpX<CONST_FINITE_MAP>(exp)) {
      return VisitAction(exp, false, m_rw);
    } else if (isOpX<GET>(exp)) {
      return VisitAction(exp, false, m_rw);
    } else if (isOpX<SET>(exp)) {
      return VisitAction(exp, false, m_rw);
    } else if (isOpX<EQ>(exp)) {
    } else if (isOpX<FAPP>(exp)) {
      return VisitAction(exp, true, m_rw); // skip kids in fapps for now
    }
    return VisitAction(exp, false, m_rw);
  }

  // // TODO: replace by FamilyId with FiniteMapOP
  // bool isFiniteMapOp(Expr e) {
  //   return isOpX<CONST_FINITE_MAP>(exp) || isOpX<GET>(exp) || isOpX<GET>(exp);
  // }
};

void transformFiniteMapsHornClauses(HornClauseDB &db, ExprFactory &efac) {

  FiniteMapTransVisitor fmv(efac);

  std::vector<HornRule> worklist;
  boost::copy(db.getRules(), std::back_inserter(worklist));

  // DagVisitCache dvc; // not used because we have to visit everything

  for (auto rule : worklist) {
    ExprVector vars = rule.vars();
    ExprSet allVars(vars.begin(), vars.end());
    // TODO: !!! the visitor needs to update these variables

    Expr new_head = visit(fmv, rule.head());
    Expr new_body = visit(fmv, rule.body());

    HornRule new_rule(allVars, new_head, new_body);
    db.removeRule(rule);
    db.addRule(new_rule);
  }
}

// TODO: this converts the output of z3 back to the original clauses with maps
class FiniteMapHornModelConverter : public HornModelConverter {
  private:
    // std::map<Expr, ExprMap> m_relToBoolToTermMap;
    // std::map<Expr, Expr> m_newToOldPredMap;
    HornClauseDB *m_abs_db;

    // std::map<Expr, ExprMap> &getRelToBoolToTermMap() {
    //   return m_relToBoolToTermMap;
    // }

  public:
    FiniteMapHornModelConverter() {}

    bool convert(HornDbModel &in, HornDbModel &out);

    // void addRelToBoolToTerm(Expr rel, ExprMap &boolToTermMap) {
    //   // m_relToBoolToTermMap.insert(std::make_pair(rel, boolToTermMap));
    // }
    // void setNewToOldPredMap(std::map<Expr, Expr> &newToOldMap) {
    //   // m_newToOldPredMap = newToOldMap;
    // }
    void setAbsDB(HornClauseDB &db) { m_abs_db = &db; }
  };

} // namespace seahorn
