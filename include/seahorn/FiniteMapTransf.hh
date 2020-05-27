#pragma once

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBind.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"
#include "seahorn/Expr/ExprVisitor.hh"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornModelConverter.hh"

#include "seahorn/Support/SeaDebug.h"

using namespace expr;
using namespace expr::op;

namespace seahorn {

struct FMapExprsInfo {

  // -- set of vars of the expression being rewritten, it will
  // be updated if new vars are needed
  ExprSet &m_vars;
  // -- to cache the type of a map expr
  ExprMap &m_type;
  // -- to cache the lambda expr generated for the keys a map type
  ExprMap &m_type_lmd;
  ExprFactory &m_efac;

  FMapExprsInfo(ExprSet &vars, ExprMap &types, ExprMap &type_lmds,
                ExprFactory &efac)
      : m_vars(vars), m_type(types), m_type_lmd(type_lmds), m_efac(efac) {}
};

// Rewrites a finite map operation to remove finite map terms. The arguments
// of the operation are assumed to be already rewritten (no finite map
// terms). The rewriter needs to be initialized for every clause
class FiniteMapRewriter : public std::unary_function<Expr, Expr> {
  // put Expr as a friend class have access to expr->args()??

  FMapExprsInfo m_fmei;

public:
  FiniteMapRewriter(ExprSet &evars, ExprMap &expr_type, ExprMap &type_lambda,
                    ExprFactory &efac)
      : m_fmei(evars, expr_type, type_lambda, efac){};

  Expr operator()(Expr exp);
};

// Top-down visitor to rewrite maps in arguments of predicate fapps
class FiniteMapArgsVisitor : public std::unary_function<Expr, VisitAction> {

private:
  const ExprMap &m_pred_decl_t;
  ExprFactory &m_efac;
  ExprSet &m_evars;

public:
  FiniteMapArgsVisitor(ExprSet &evars, const ExprMap &pred_decl_t,
                       ExprFactory &efac)
      : m_evars(evars), m_pred_decl_t(pred_decl_t), m_efac(efac) {}

  VisitAction operator()(Expr exp);
};

// Bottom-up visitor to rewrite maps in bodies
class FiniteMapBodyVisitor : public std::unary_function<Expr, VisitAction> {

private:
  ExprMap m_types;
  ExprMap m_map_lambda;
  std::shared_ptr<FiniteMapRewriter> m_rw;

public:
  FiniteMapBodyVisitor(ExprSet &evars, ExprFactory &efac) {
    m_rw =
        std::make_shared<FiniteMapRewriter>(evars, m_types, m_map_lambda, efac);
  }

  VisitAction operator()(Expr exp);

private:
  bool isVisitFiniteMapOp(Expr e);
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
