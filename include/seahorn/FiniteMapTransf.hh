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

using KeysPair = std::pair<ExprVector, Expr>;
using KeysStack = std::vector<KeysPair>;

// Rewrites a finite map operation whose arguments are already rewritten
// The rewriter needs to be initialized for every clause
// TODO: rename by FiniteMapClauseRewriter?
struct FiniteMapTransRewriter : public std::unary_function<Expr, Expr> {
  // put Expr as a friend class have access to expr->args()??

  HornClauseDB &m_db;
  ExprSet m_evars; // set of vars of the expression being rewritten, it will be
                   // updated if new vars are needed
  ExprFactory &m_efac;

  // ExprMap m_fmapvars_keys;
  ExprMap &m_fmapvars_vals;

  // Used as a stack to keep the keys of the children
  KeysStack &m_keys_children;

  FiniteMapTransRewriter(ExprFactory &efac, KeysStack &mkeys, HornClauseDB &db,
                         ExprSet evars, ExprMap fmapvars_vals)
      : m_efac(efac), m_keys_children(mkeys), m_db(db), m_evars(evars),
        m_fmapvars_vals(fmapvars_vals){};

  Expr operator()(Expr exp) {
    // errs() << "Rewritting " << *exp << "\n";
    Expr res;
    if (isOpX<CONST_FINITE_MAP>(exp)) {
      ExprVector keys(exp->args_begin(), exp->args_end());
      m_keys_children.push_back(
          { keys, finite_map::make_lambda_map_keys(keys, m_efac) });
      Expr lkeys = finite_map::make_lambda_map_keys(keys, m_efac);
      errs() << "-> Push: " << *lkeys << "\n";
      res = finite_map::empty_map_lambda(m_efac);
    } else if (isOpX<GET>(exp)) {
      assert(!m_keys_children.empty()); // check that it has
      Expr map = exp->left();
      if(bind::isFiniteMapConst(map)) // the map is a variable
        res = finite_map::make_var_key(map, exp->right(), m_evars);
      else { // the map is an ite expression or '0' (empty map)
        KeysPair keys_child = m_keys_children.back();
        Expr lmd_keys = keys_child.second;
        res = finite_map::get_map_lambda(map, lmd_keys, exp->right());
      }
      m_keys_children.pop_back();
    } else if (isOpX<SET>(exp)) {
      assert(!m_keys_children.empty());
      KeysPair keys_child = m_keys_children.back();
      Expr lmd_keys = keys_child.second;
      ExprVector args(exp->args_begin(), exp->args_end());
      Expr map = exp->left();
      if (bind::isFiniteMapConst(map)){ // the map is a variable
        ExprVector svals;
        for (auto k : keys_child.first)
          svals.push_back(finite_map::make_var_key(map, k, m_evars));
        // create map with symbolic values
        map = finite_map::make_map_batch_values(keys_child.first, svals, m_efac, lmd_keys);
      }
      Expr value = args[2]; // TODO: can this be done without building args?
      res = finite_map::set_map_lambda(map, lmd_keys,
                                       exp->right(), value, m_efac);
    } else if (bind::isFiniteMapConst(exp)){
      errs() << "Map const found\n";
      Expr name = bind::fname(exp);
      Expr mTy = bind::rangeTy(name);
      ExprVector keys(mTy->args_begin(), mTy->args_end()); // warning, local variable!!!!
      Expr lmd_keys = finite_map::make_lambda_map_keys(keys, m_efac);
      errs() << "-> Push: " << *lmd_keys << "\n";
      m_keys_children.push_back(
          {ExprVector(mTy->args_begin(), mTy->args_end()),
           finite_map::make_lambda_map_keys(keys, m_efac)});
      res = exp; // return the fmap variable as it is
    } else if (isOpX<EQ>(exp)) {
      errs() << "Rewritting EQ: exp" << *exp << "\n";
      Expr el = exp->left();
      Expr er = exp->right();

      errs() << "left: " << *el << "\n";
      errs() << "right: " << *er << "\n";

      // the maps are already ite, how can I know the types?
      assert(m_keys_children.size() >= 2);

      // ExprVector keys2 = m_keys_children.back().first;
      Expr lkeys2 = m_keys_children.back().second;
      errs() << "lkeys2: " << *lkeys2 << "\n";
      m_keys_children.pop_back();

      ExprVector keys1 = m_keys_children.back().first;
      Expr lkeys1 = m_keys_children.back().second;
      errs() << "lkeys1: " << *lkeys1 << "\n";
      m_keys_children.pop_back();

      assert(lkeys1);
      assert(lkeys2);

      // to check this, they would need to be sorted first
      // assert(keys1 == keys2);
      res = finite_map::make_eq_maps_lambda(el, lkeys1, er, lkeys2, keys1,
                                            m_efac, m_evars);
    } else { // do nothing
      errs() << "Unexpected map expression: " << *exp << "\n"; // TODO put in log
      assert(false && "Unexpected map expression");
      return exp;
    }
    errs() << "Rewritten: " << *exp << "\n   to: " << *res << "\n"; // TODO: put in
                                                                 // log
    return res;
  }
};
struct FiniteMapTransVisitor : public std::unary_function<Expr, VisitAction> {

  KeysStack fmap_keys;
  ExprMap map_vals;
  ExprFactory &m_efac;
  std::shared_ptr<FiniteMapTransRewriter> m_rw;

  FiniteMapTransVisitor(ExprFactory &efac, HornClauseDB &db, ExprSet evars)
      : m_efac(efac) {
    m_rw = std::make_shared<FiniteMapTransRewriter>(m_efac, fmap_keys, db, evars, map_vals);
  }
  VisitAction operator()(Expr exp) {
    errs() << "Creating visit action for: " << *exp << "\n";
    if (isFiniteMapOp(exp)) {
      errs() << "---FiniteMapOp\n";
      return VisitAction::changeDoKidsRewrite(exp, m_rw);
    } else if (bind::isFiniteMapConst(exp)) {
      errs() << "---FiniteMapConst\n";
      return VisitAction(exp, false, m_rw);
    } else if (bind::isConst(exp)) {
      errs() << "---No rewritting\n";
      return VisitAction::skipKids();
      // TODO Jorge: if set to true it is not rewritten!!
    } else if (isOpX<EQ>(exp)) {
      errs() << "---EQ\n";
      if (returnsFiniteMap(exp->left()) || returnsFiniteMap(exp->right()))
        return VisitAction::changeDoKidsRewrite(exp, m_rw);
    } else if (isOpX<FAPP>(exp)) {
      errs() << "---FAPP\n";
      // return VisitAction::changeDoKidsRewrite(exp, m_rw); // not implemented yet
    }
    errs() << "---No rewritting\n";
    // This step doesn't need to be rewritten but the kids do
    return VisitAction::changeDoKids(exp);
  }

  // TODO: replace by FamilyId with FiniteMapOP?
  bool isFiniteMapOp(Expr e) {
    return isOpX<CONST_FINITE_MAP>(e) || isOpX<GET>(e) || isOpX<SET>(e);
  }

  bool returnsFiniteMap(Expr e) {
    return isOpX<CONST_FINITE_MAP>(e) || isOpX<SET>(e) || bind::isFiniteMapConst(e);
  }
};

void transformFiniteMapsHornClauses(HornClauseDB &db, ExprFactory &efac) {

  std::vector<HornRule> worklist;
  boost::copy(db.getRules(), std::back_inserter(worklist));

  // DagVisitCache dvc; // not used because we have to visit everything

  for (auto rule : worklist) {
    ExprVector vars = rule.vars();
    ExprSet allVars(vars.begin(), vars.end());

    FiniteMapTransVisitor fmv(efac, db, allVars);

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
