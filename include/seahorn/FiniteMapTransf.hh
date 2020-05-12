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
// The rewriter needs to be initialized for every clause
class FiniteMapRewriter : public std::unary_function<Expr, Expr> {
  // put Expr as a friend class have access to expr->args()??

  ExprSet &m_evars; // set of vars of the expression being rewritten, it will
  // be updated if new vars are needed
  ExprFactory &m_efac;

  // -- to cache the type of a map expr
  ExprMap &m_expr_type;
  // -- to cache the lambdas generated for a map type
  ExprMap &m_type_lambda;

public:
  FiniteMapRewriter(ExprFactory &efac, ExprSet &evars, ExprMap &expr_type,
                    ExprMap &type_lambda)
      : m_efac(efac), m_evars(evars), m_expr_type(expr_type),
        m_type_lambda(type_lambda){};

  Expr operator()(Expr exp);
};


// Top-down visitor to rewrite maps in arguments of predicate fapps
class FiniteMapArgsVisitor : public std::unary_function<Expr, VisitAction> {

private:
  const ExprMap &m_pred_decl_t;
  ExprFactory &m_efac;
  ExprSet &m_evars;

public:
  FiniteMapArgsVisitor(ExprFactory &efac, ExprSet &evars,
                       const ExprMap &pred_decl_t)
      : m_efac(efac), m_evars(evars), m_pred_decl_t(pred_decl_t) {}

  VisitAction operator()(Expr exp);
};

// Bottom-up visitor to rewrite maps in bodies
class FiniteMapBodyVisitor : public std::unary_function<Expr, VisitAction> {

private:
  ExprMap m_exp_types;
  ExprMap m_map_lambda;
  std::shared_ptr<FiniteMapRewriter> m_rw;

public:
  FiniteMapBodyVisitor(ExprFactory &efac, ExprSet &evars) {
    m_rw = std::make_shared<FiniteMapRewriter>(efac, evars, m_exp_types,
                                               m_map_lambda);
  }

  VisitAction operator()(Expr exp);

  // TODO: replace by FamilyId with FiniteMapOP?
  bool isFiniteMapOp(Expr e) {
    return isOpX<CONST_FINITE_MAP_KEYS>(e) || isOpX<CONST_FINITE_MAP>(e) ||
           isOpX<GET>(e) || isOpX<SET>(e);
  }

};


// TODO: this converts the output of z3 back to the original clauses
// with maps
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