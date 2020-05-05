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

namespace{
  template <typename T> bool compare(std::vector<T> &v1, std::vector<T> &v2) {
    std::sort(v1.begin(), v1.end());
    std::sort(v2.begin(), v2.end());
    return v1 == v2;
  }
}
namespace seahorn {

using TypesStack = std::vector<Expr>;

// struct FiniteMapPredicateRewriter : public std::unary_function<Expr, Expr> {
//   HornClauseDB &m_db;
//   ExprSet m_evars; // set of vars of the expression being rewritten, it will
//                    // be updated if new vars are needed
//   ExprFactory &m_efac;

//   TypesStack &m_types_children;

//   FiniteMapPredicateRewriter(TypesStack &mkeys, HornClauseDB &db, ExprSet evars,
//                              ExprMap fmapvars_vals)
//       : m_efac(db.getExprFactory()), m_types_children(mkeys), m_db(db),
//         m_evars(evars), m_fmapvars_vals(fmapvars_vals) {}

//   Expr operator()(Expr exp){
//     return res;
//   }
// };

// Rewrites a finite map operation whose arguments are already rewritten
// The rewriter needs to be initialized for every clause
// TODO: rename by FiniteMapClauseRewriter?
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

  // Expr m_value_tag = nullptr;
  // Expr m_key_tag = nullptr;

  Expr m_boolTy = nullptr;
  Expr m_intTy = nullptr;
  // TODO: add missing types?

  FiniteMapRewriter(TypesStack &mkeys, HornClauseDB &db, ExprSet evars,
                    ExprMap type_lambda)
      : m_efac(db.getExprFactory()), m_types_children(mkeys), m_db(db),
        m_evars(evars), m_type_lambda(type_lambda) {
    // TODO: performance!!!!!!
    // m_value_tag = mkTerm<std::string>("v", m_efac); // TODO: replace this
    // m_key_tag = mkTerm<std::string>("k", m_efac);
    m_boolTy = sort::boolTy(m_efac);
  };

  Expr operator()(Expr exp) {
      Expr res;
      if (isOpX<CONST_FINITE_MAP>(exp)) {
        Expr mapTy = bind::type(exp);
        m_types_children.push_back(mapTy);
        ExprVector keys(exp->args_begin(), exp->args_end());
        m_type_lambda[mapTy] = finite_map::make_lambda_map_keys(keys, m_efac);
        Expr lkeys = finite_map::make_lambda_map_keys(keys, m_efac);
        errs() << "-> Push: " << *lkeys << "\n";
        res = finite_map::empty_map_lambda(m_efac);

      } else if (isOpX<GET>(exp)) {
        assert(!m_types_children.empty()); // check that it has
        Expr map = exp->left();
        if (bind::isFiniteMapConst(map)) { // the map is a variable
          res = finite_map::make_variant_key(map, exp->right());
          m_evars.insert(res); // insert for later
        } else { // the map is an already expanded map expression
          Expr mapTy = m_types_children.back();
          Expr lmdKeys = m_type_lambda[mapTy];
          res = finite_map::get_map_lambda(map, lmdKeys, exp->right());
        }
        m_types_children.pop_back();
        m_types_children.push_back(m_intTy);

      } else if (isOpX<SET>(exp)) {
        m_types_children.pop_back(); // extract value type
        m_types_children.pop_back(); // extract key type
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
          map = finite_map::make_map_batch_values(mkeys, svals,
                                                  m_efac, lmd_keys);
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

        errs() << "-> Push: " << *lmd_keys << "\n";
        m_types_children.push_back(mTy);

        if (m_type_lambda.count(mTy) == 0) // is it necessary?, cheaper to just
                                           // overwrite with the same?
          m_type_lambda[mTy] = finite_map::make_lambda_map_keys(keys, m_efac);

        res = exp; // return the fmap variable as it is
      }
      else if (bind::isConst(exp)) {
        Expr type = bind::type(bind::name(exp));
        m_types_children.push_back(type);
        errs() << "Push: " << *type << "\n";
        res = exp;
      } else if (isOpX<EQ>(exp)) {

        assert(m_types_children.size() >= 2);
        Expr el = exp->left();
        Expr er = exp->right();

        Expr Ty2 = m_types_children.back();
        m_types_children.pop_back();
        Expr Ty1 = m_types_children.back();
        m_types_children.pop_back();

        if (returnsFiniteMap(el) || returnsFiniteMap(el)) {
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
      } else {
          // assert(typeOf(t1) == typeOf(t2)); // check that they have the same
          // types
          errs() << "Checking if " << *Ty1 << " == " << *Ty2 << "\n";
          res = exp;
        }
      // push type of eq
        m_types_children.push_back(m_boolTy);
        errs() << "Push: " << *m_boolTy << "\n";
    }
    // else if (isOpX<FAPP>(exp)) {
    //   // prepare types:
    //   errs() << "types" << *bind::type(exp);
    //   Expr type = bind::type(exp);
    //   Expr fTy = bind::rangeTy(type);

    //   errs() << "fname" << *bind::fname(exp);
    //   Expr fapp = bind::rangeTy(bind::fname(exp));
    //   Expr fname = bind::name(fapp);

    //   Expr iTy = sort::intTy(m_efac);
    //   ExprVector newArgs;
    //   ExprVector newTypes;
    //   ExprVector newLits;

    //   // these iterators start from the end because we are using a stack
    //   auto arg_it = fapp->args_end(), t_it = fTy->args_end();
    //   for (; t_it != fTy->args_begin(); t_it--) {
    //     assert(arg_it != fapp->args_begin());
    //     Expr argTy = *t_it;
    //     if (isOpX<FINITE_MAP_TY>(argTy)) { // this cannot happen in the second round
    //       bool notMapConst = !bind::isFiniteMapConst(*arg_it);
    //       // extract from the stack the lmd_keys of the arg,
    //       for (auto key_it = (*t_it)->args_begin();
    //            key_it != (*t_it)->args_end(); key_it++) {

    //         Expr newA =
    //             finite_map::make_variant_key(*arg_it, *key_it);
    //         newArgs.push_back(newA);
    //         newTypes.push_back(iTy);
    //         if (notMapConst) {
    //           Expr mTy = m_types_children.back();
    //           Expr lmd_keys = m_type_lambda[mTy];
    //           newLits.push_back(mk<EQ>(newA, finite_map::get_map_lambda(
    //                                              *arg_it, lmd_keys, *key_it)));
    //         }
    //       }
    //       m_types_children.pop_back();
    //     } else {
    //       newArgs.push_back(*arg_it);
    //       newTypes.push_back(argTy);
    //     }
    //     arg_it--;
    //     m_types_children.pop_back();
    //   }
    //   // new fdecl // TODO: modify name to avoid confusion?
    //   Expr fdecl = bind::fdecl(fname, newTypes);
    //   res = mk<AND>(mknary<AND>(newLits), bind::fapp(fdecl, newArgs));

    //   // push return type of FAPP
    //   m_types_children.push_back(bind::typeOf(exp));
    // }
    else { // do nothing
      assert(false && "Unexpected map expression");
      return exp;
    }
    errs() << "Rewritten: " << *exp << "\n   to: " << *res << "\n"; // TODO: LOG
    return res;
  }
  bool returnsFiniteMap(Expr e) {
    return isOpX<CONST_FINITE_MAP>(e) || isOpX<SET>(e) ||
      bind::isFiniteMapConst(e);
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

struct FiniteMapPredicateVisitor
    : public std::unary_function<Expr, VisitAction> {

  TypesStack fmap_keys;
  ExprMap map_vals;
  std::shared_ptr<FiniteMapRewriter> m_rw;

  FiniteMapPredicateVisitor(HornClauseDB &db, ExprSet evars) {
    m_rw = std::make_shared<FiniteMapRewriter>(fmap_keys, db, evars, map_vals);
  }

  VisitAction operator()(Expr exp) {
    if (isOpX<FAPP>(exp))
      return VisitAction::changeDoKidsRewrite(exp, m_rw);
    else
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
        return VisitAction::changeDoKidsRewrite(exp, m_rw);
      } else if (isOpX<EQ>(exp)) {
        // if (returnsFiniteMap(exp->left()) || returnsFiniteMap(exp->right()))
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
    Expr newPredDecl = processMapsRel(predDecl, db.getExprFactory());

    // get clauses in pred definition, requires indexes (see
    // buildIndexes())
    auto HCDefSet = db.def(predDecl);

    // change the rules in this predicate
    for (auto rule : HCDefSet) {
      // be careful here because the rule may be a fact
      const ExprVector &vars = rule->vars();
      ExprSet allVars(vars.begin(), vars.end());

      // only changes the head, adding needed unifications to the body
      FiniteMapPredicateVisitor fmv(db, allVars); // updates the variables
      db.addRule(allVars, visit(fmv, rule->get()));
      const HornRule r = *rule;
      db.removeRule(r);
    }

    // get clauses that calls this predicate
    auto HCUseSet = db.use(predDecl);

    for (auto rule : HCUseSet) {
      const ExprVector &vars = rule->vars();
      ExprSet allVars(vars.begin(), vars.end());

      // only changes the calls in the body, adding needed unifications
      FiniteMapPredicateVisitor fmv(db, allVars); // updates the variables
      // initialize it with the predicate that we want to process!! and use only
      // one visitor

      HornRule newRule(allVars, visit(fmv, rule->get()));
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
