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

// just for checking if two sets of keys are the same, only use in debug mode
namespace{
  template <typename T> bool compare(std::vector<T> &v1, std::vector<T> &v2) {
    std::sort(v1.begin(), v1.end());
    std::sort(v2.begin(), v2.end());
    return v1 == v2;
  }
}
namespace seahorn {

bool returnsFiniteMap(Expr e) {
  return isOpX<CONST_FINITE_MAP>(e) || isOpX<SET>(e) ||
         bind::isFiniteMapConst(e);
}

using TypesStack = std::vector<Expr>;

// Rewrites a finite map operation whose arguments are already rewritten
// The rewriter needs to be initialized for every clause
struct FiniteMapRewriter : public std::unary_function<Expr, Expr> {
  // put Expr as a friend class have access to expr->args()??

  HornClauseDB &m_db;
  ExprSet m_evars; // set of vars of the expression being rewritten, it will
  // be updated if new vars are needed
  ExprFactory &m_efac;

  // -- to cache the lambdas generated for a map type
  ExprMap &m_type_lambda;

  // Used as a stack to keep the keys of the children
  TypesStack &m_types_children;

  FiniteMapRewriter(TypesStack &mkeys, HornClauseDB &db, ExprSet evars,
                    ExprMap type_lambda)
      : m_efac(db.getExprFactory()), m_types_children(mkeys), m_db(db),
        m_evars(evars), m_type_lambda(type_lambda) { };

  Expr operator()(Expr exp) {
    Expr res;
    if (isOpX<CONST_FINITE_MAP>(exp)) {
      Expr mapTy = bind::type(exp);
      m_types_children.push_back(mapTy);
      ExprVector keys(exp->args_begin(), exp->args_end());
      m_type_lambda[mapTy] = finite_map::make_lambda_map_keys(keys, m_efac);
      errs() << "-> Push: " << *m_type_lambda[mapTy] << "\n";
      res = finite_map::empty_map_lambda(m_efac);

    } else if (isOpX<GET>(exp)) {
      assert(!m_types_children.empty()); // check that it has a map
      Expr map = exp->left();
      if (bind::isFiniteMapConst(map)) { // the map is a variable
        res = finite_map::make_variant_key(map, exp->right());
        m_evars.insert(res); // insert for later
      } else {   // the map is an already expanded map expression
        Expr mapTy = m_types_children.back();
        Expr lmdKeys = m_type_lambda[mapTy];
        assert(!lmdKeys);
        res = finite_map::get_map_lambda(map, lmdKeys, exp->right());
      }
      m_types_children.pop_back();
      // m_types_children.push_back(m_intTy);

    } else if (isOpX<SET>(exp)) {
      // m_types_children.pop_back(); // extract value type
      // m_types_children.pop_back(); // extract key type
      assert(!m_types_children.empty());

      Expr mapTy = m_types_children.back(); // get map type
      Expr lmd_keys = m_type_lambda[mapTy];
      assert(!lmd_keys);
      ExprVector args(exp->args_begin(), exp->args_end());

      Expr map = args[0];

      if (bind::isFiniteMapConst(map)) { // operating with a map variable
        ExprVector mkeys(mapTy->args_begin(), mapTy->args_begin());
        ExprVector svals;
        for (auto k : mkeys) {
          Expr aux_var = finite_map::make_variant_key(map, k);
          svals.push_back(aux_var);
          m_evars.insert(aux_var);
        }
        // create map with symbolic values
        map = finite_map::make_map_batch_values(mkeys, svals, m_efac, lmd_keys);
      }
      Expr key = args[1];
      Expr value = args[2]; // TODO: can this be done without building args?
      res = finite_map::set_map_lambda(map, lmd_keys, key, value, m_efac);

      // set returns a map with the same keys, so it is not necessary to pop to
      // push the same map in m_types_children

    } else if (bind::isFiniteMapConst(exp)) {

      Expr name = bind::fname(exp);
      Expr mTy = bind::rangeTy(name);
      ExprVector keys(mTy->args_begin(),
                      mTy->args_end()); // warning, local variable!!!!
      Expr lmd_keys = finite_map::make_lambda_map_keys(keys, m_efac);

      errs() << "-> Push: " << *mTy << "\n";
      m_types_children.push_back(mTy);

      if (m_type_lambda.count(mTy) == 0) // is it necessary?, cheaper to just
                                         // overwrite with the same?
        m_type_lambda[mTy] = finite_map::make_lambda_map_keys(keys, m_efac);

      res = exp; // return the fmap variable as it is
    }  else if (isOpX<EQ>(exp)) {

      assert(m_types_children.size() >= 2);
      Expr el = exp->left();
      Expr er = exp->right();
      if (returnsFiniteMap(el) || returnsFiniteMap(el)) {
        Expr Ty2 = m_types_children.back();
        m_types_children.pop_back();
        Expr Ty1 = m_types_children.back();
        m_types_children.pop_back();

        Expr lkeys2 = m_type_lambda[Ty2];
        Expr lkeys1 = m_type_lambda[Ty1];

        assert(lkeys1);
        assert(lkeys2);
        // only one keys vector is needed, just done for compare
        ExprVector keys1(Ty1->args_begin(), Ty1->args_end());
        ExprVector keys2(Ty2->args_begin(), Ty2->args_end());
        assert(compare(keys1, keys2));
        // check that both maps have the same keys
        res = finite_map::make_eq_maps_lambda(el, lkeys1, er, lkeys2, keys1,
                                              m_efac, m_evars);
      }
    } else if (isOpX<FAPP>(exp)) {
      
    } else { // do nothing
      assert(false && "Unexpected map expression");
      return exp;
    }
    errs() << "Rewritten: " << *exp << "\n   to: " << *res << "\n"; // TODO: LOG
    return res;
  }
};


Expr headFiniteMapRewriter(Expr oldHead, Expr newFdecl, ExprSet &vars,
                           ExprFactory &efac, ExprVector &extraUnifs) {

  assert(isOpX<FAPP>(oldHead));

  Expr fdecl = bind::name(oldHead);
  assert(bind::isFdecl(fdecl));
  Expr fname = bind::fname(fdecl);

  ExprVector newArgs;

  auto arg_it = ++(oldHead->args_begin()), t_it = ++(fdecl->args_begin());
  if (arg_it == oldHead->args_end()) // no args
    return oldHead;

  int arg_count = 0;
  for (; arg_it != oldHead->args_end(); arg_it++, arg_count++) {
    Expr arg = *arg_it;
    Expr argTy = *t_it;
    errs() << "\t processing: " << *arg << " of type " << *argTy << "\n"; // LOG

    if (isOpX<FINITE_MAP_TY>(argTy)) {
      Expr map_vars_name;
      if (bind::isFiniteMapConst(arg)) {
        map_vars_name = bind::name(arg); // TODO: check this
      }
      else{
        map_vars_name = variant::variant(arg_count,fname);
        // if there is no name, we create a variant with the name of the
        // function, make new variable (same as normalization)
      }
      Expr mTy = *t_it;
      ExprVector keys(mTy->args_begin(), mTy->args_end());
      Expr lmdks = finite_map::make_lambda_map_keys(keys,efac);
      finite_map::expand_map_vars(arg, lmdks, keys, newArgs, extraUnifs, efac, vars);
    } else {
      newArgs.push_back(arg);
    }
  }
  return bind::fapp(newFdecl, newArgs);
}

struct FiniteMapArgsVisitor : public std::unary_function<Expr, VisitAction> {

  Expr m_new_fdecl;
  HornClauseDB &m_db;
  ExprSet &m_evars;

  FiniteMapArgsVisitor(HornClauseDB &db, ExprSet &evars, Expr new_fdecl)
    : m_db(db), m_new_fdecl(new_fdecl), m_evars(evars) {}

  VisitAction operator()(Expr exp) {
    if (isOpX<FAPP>(exp)){
      Expr fdecl = bind::name(exp);
      if (m_db.hasRelation(fdecl)){
        // TODO: check that it is the relation that we are rewriting. Assume
        // different relations have different names?
        ExprVector newUnifs;
        Expr newFapp = headFiniteMapRewriter(exp, m_new_fdecl, m_evars, m_db.getExprFactory(), newUnifs);
        Expr newExp = mk<AND>(mknary<AND>(newUnifs), newFapp);
        return VisitAction::changeDoKids(newExp);
      }
    }

    return VisitAction::changeDoKids(exp);
  }
};

  struct FiniteMapBodyVisitor : public std::unary_function<Expr, VisitAction> {

    TypesStack m_types;
    ExprMap m_map_vals;
    std::shared_ptr<FiniteMapRewriter> m_rw;

    FiniteMapBodyVisitor(HornClauseDB &db, ExprSet evars) {
      m_rw =
          std::make_shared<FiniteMapRewriter>(m_types, db, evars, m_map_vals);
    }
    VisitAction operator()(Expr exp) {
      // errs() << "Creating visit action for: " << *exp << "\n";
      if (isFiniteMapOp(exp)) {
        return VisitAction::changeDoKidsRewrite(exp, m_rw);
      } else if (bind::isFiniteMapConst(exp)) {
        return VisitAction::changeDoKidsRewrite(exp, m_rw);
      } else if (bind::isConst(exp)) {
        return VisitAction::skipKids();
      } else if (isOpX<EQ>(exp)) {
        if (returnsFiniteMap(exp->left()) || returnsFiniteMap(exp->right()))
          return VisitAction::changeDoKidsRewrite(exp, m_rw);
    } else if (isOpX<FAPP>(exp)) { // TODO: check arity > 0
      // do nothing because it is processed in the first transformation
      // return VisitAction::skipKids();
    } else if (bind::isFdecl(exp)) {
      // errs() << "skip kids\n";
      return VisitAction::skipKids();
    }
    // This step doesn't need to be rewritten but the kids do
    return VisitAction::changeDoKids(exp);
  }

  // TODO: replace by FamilyId with FiniteMapOP?
  bool isFiniteMapOp(Expr e) {
    return isOpX<CONST_FINITE_MAP>(e) || isOpX<GET>(e) || isOpX<SET>(e);
  }

};

Expr processMapsRel(Expr fdecl, ExprFactory &efac){

  assert(isOpX<FDECL>(fdecl));

  ExprVector oldTypes;
  ExprVector newTypes;

  Expr iTy = op::sort::intTy(efac);
  Expr fname = bind::fname(fdecl);

  for (auto tyIt = fdecl->args_begin(); tyIt != fdecl->args_end(); tyIt++) {
    Expr type = *tyIt;
    if (isOpX<FINITE_MAP_TY>(type)) { // the type is a FiniteMap
      assert(type->args_begin() != type->args_end()); // the map has at
                                                      // least one key
      for (auto kIt = type->args_begin(); kIt != type->args_end() ; kIt++) {
        newTypes.push_back(iTy); // new argument for key
        newTypes.push_back(iTy); // new argument for value
      }
    }
    else
      newTypes.push_back(type);
  }

  Expr newfname = fdecl; // to go back easier, the new name includes the
                         // old declaration

  return bind::fdecl(newfname, newTypes);

}

void removeFiniteMapsArgsHornClausesTransf(HornClauseDB &db) {

  ExprFactory &efac = db.getExprFactory();

  // std::vector<Expr> worklist;
  ExprVector worklist;
  boost::copy(db.getRelations(), std::back_inserter(worklist));

  db.buildIndexes(); // how often do these indexes need to be rebuilt?, we are
                     // inserting the same clause several times, maybe update
                     // the indexes while inserting/removing a clause?

  for (auto predIt : worklist) {
    Expr predDecl = predIt;

      // create new relation declaration
    Expr newPredDecl = processMapsRel(predDecl, efac);

    // get clauses in pred definition, requires indexes (see
    // buildIndexes())
    auto HCDefSet = db.def(predDecl);

    // change the rules in this predicate
    for (auto rule : HCDefSet) {
      // be careful here because the rule may be a fact
      const ExprVector &vars = rule->vars();
      ExprSet allVars(vars.begin(), vars.end());

      ExprVector newUnifs;      // This will be added to the body
      Expr head = rule->head();
      Expr newHead = headFiniteMapRewriter(head,newPredDecl, allVars, efac, newUnifs);

      FiniteMapArgsVisitor fmav(db,allVars,newPredDecl);
      Expr body = rule->body(); // TODO: change this
      Expr tmpBody = visit(fmav, body);
      // include new unificatons for the head
      Expr newBody = mk<AND>(mknary<AND>(newUnifs),tmpBody);
      db.addRule(allVars, boolop::limp(newBody, newHead));
      const HornRule r = *rule;
      db.removeRule(r);
    }

    // get clauses that calls this predicate
    auto HCUseSet = db.use(predDecl);

    for (auto rule : HCUseSet) {
      const ExprVector &vars = rule->vars();
      ExprSet allVars(vars.begin(), vars.end());

      // only changes the calls in the body, adding needed unifications
      FiniteMapArgsVisitor fmav(db, allVars, newPredDecl);
      // initialize it with the predicate that we want to process!! and use
      // only one visitor

      HornRule newRule(allVars, visit(fmav, rule->get()));
      db.addRule(newRule);

      db.removeRule(*rule);
    }
    db.registerRelation(newPredDecl);
    // remove old relation declaration
    // db.m_rels.remove(predIt) // (not public)
  }
}

void removeFiniteMapsBodiesHornClausesTransf(HornClauseDB &db) {

  ExprFactory &efac = db.getExprFactory();

  std::vector<HornRule> worklist;
  boost::copy(db.getRules(), std::back_inserter(worklist));

  // DagVisitCache dvc; // not used because we have to visit everything

  // 2 steps:
  // - prepare new predicate signatures and rewrite rules
  // - perform local transformation

  for (auto rule : worklist) {
    ExprVector vars = rule.vars();
    ExprSet allVars(vars.begin(), vars.end());

    FiniteMapBodyVisitor fmv(db, allVars);

    // map old predicates to new ones, and rewrite by predicate, not rule
    Expr new_head = visit(fmv, rule.head());
    // TODO only once
    // * register relation with new parameters in db
    // * "unregister" old relation?
    Expr new_body = visit(fmv, rule.body());

    HornRule new_rule(allVars, new_head, new_body);
    db.removeRule(rule);
    db.addRule(new_rule);
  }
}

    // f(map_a, k1, x) :- x = get(map_a, k1), g(map_a).
    // F(map_a_k1_v, k1, k1, x) :- map_a = defk(k1,map_a_k1_v), x = get(map_a,
    // k1),
    //                             G(map_a_k1_v, k1).

    // f(map_b, k1, x) :- map_b = set(map_a, k1, +(get(map_a, k1), 1)),
    // g(map_a).
    //
    // F(map_b_k1_v, k1, k1, x) :- map_b = defk(k1,map_b_k1_v), // side
    // condition
    //                             map_b = set(map_a, k1, +(get(map_a, k1), 1)),
    //                             map_a = defk(k1,map_a_k1_v), // side
    //                             condition G(map_a_k1_v, k1).

    // (f x) < -((map1 = set(defk(k1, k2), k1, 42)) && (x = get(map1, k1)))

    // (f x) <- (((|get(map1,k1)|=ite(ite(k2=k1, 2, ite(k1=k1, 1, 0))=ite(k2=k1,
    // 2, ite(k1=k1, 1, 0)), 42, 0))&&(|get(map1,k2)|=ite(ite(k2=k2, 2,
    // ite(k1=k2, 1, 0))=ite(k2=k1, 2, ite(k1=k1, 1, 0)), 42, 0)))&&
    // (x=|get(map1,k1)|)).

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
