#include "seahorn/FiniteMapTransf.hh"

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprOpBind.hh"
#include "seahorn/Expr/ExprCore.hh"
// #include "seahorn/Expr/ExprOpFiniteMap.hh"
#include "seahorn/Expr/ExprVisitor.hh"
// #include "seahorn/HornClauseDB.hh"
// #include "seahorn/HornModelConverter.hh"


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

  Expr mkVarGet(Expr m1, Expr k) {
  // TODO: replace by |get(m1,k)|
    return bind::intConst(variant::tag(m1, k));
  }

// check that one maps contains the same values as another. Both maps are
// assumed to have the same keys `keys` but not necessarily in the same order,
// that is why `ks1` and `ks2` are needed.
//
// old make_eq_maps_lambda
Expr mkEqCore(Expr m1, Expr ks1, Expr m2, Expr ks2, ExprVector &keys,
          ExprFactory &efac, ExprSet &evars) {

  ExprVector conj;

  bool is_var_m1 = bind::isFiniteMapConst(m1);
  bool is_var_m2 = bind::isFiniteMapConst(m2);

  Expr e_m1, e_m2;

  for (auto k : keys) {
    if (is_var_m1) {
      e_m1 = mkVarGet(m1, k);
      evars.insert(e_m1);
    }
    else
      e_m1 = finite_map::mkGetVal(m1, ks1, k);

    if(is_var_m2) {
      e_m2 = mkVarGet(m2, k);
      evars.insert(e_m2);
    }
    else
      e_m2 = finite_map::mkGetVal(m2, ks2, k);
    conj.push_back(mk<EQ>(e_m1, e_m2));
  }
  return mknary<AND>(conj);
}

 Expr mkMapPrimitiveArgCore(Expr map, ExprFactory &efac) {
   // TODO: include also the other primitive to create the map
  if (isOpX<CONST_FINITE_MAP_KEYS>(map))
    return finite_map::mkEmptyMap(efac);
  else if (isOpX<CONST_FINITE_MAP>(map)){
    Expr keysE = map->left();
    Expr valuesE = map->right();
    ExprVector keys(keysE->args_begin(), keysE->args_begin());
    Expr lmdKeys = finite_map::mkKeys(keys, efac);
    ExprVector values(valuesE->args_begin(), valuesE->args_end());
    return finite_map::mkInitializedMap(keys, values, efac, lmdKeys);
  }
  else return map; // already transformed map
}

// old expand_map_vars
// \brief expands a map into separate scalar variables
void mkVarsMap(Expr map, Expr lmdks, ExprVector &keys,
               ExprVector &new_vars, ExprVector &extra_unifs,
               ExprFactory &efac, ExprSet &evars) {

  Expr v, v_get;

  ExprVector map_values;

  for (auto k : keys) {
    v = mkVarGet(map, k);
    evars.insert(v);

    new_vars.push_back(k);
    new_vars.push_back(v);

    map_values.push_back(v);
    // v_get = get(map, k);
  }
  extra_unifs.push_back(mk<EQ>(map, finite_map::constFiniteMap(keys,map_values)));
}

// \brief expands the map arguments of fapps into separate scalar variables
Expr mkFappArgs(Expr fapp, Expr newFdecl, ExprSet &vars, ExprFactory &efac,
                ExprVector &extraUnifs) {

  assert(isOpX<FAPP>(fapp));

  Expr fdecl = bind::name(fapp);
  assert(bind::isFdecl(fdecl));
  Expr fname = bind::fname(fdecl);

  ExprVector newArgs;

  auto arg_it = ++(fapp->args_begin()), t_it = ++(fdecl->args_begin());
  if (arg_it == fapp->args_end()) // no args
    return fapp;

  int arg_count = 0;
  for (; arg_it != fapp->args_end(); arg_it++, arg_count++, t_it++) {
    Expr arg = *arg_it;
    Expr argTy = *t_it;

    // LOG("fmap_transf",
    //     errs() << "\t processing: " << *arg << " of type " << *argTy << "\n";);

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
      Expr lmdks = finite_map::mkKeys(keys,efac);
      mkVarsMap(arg, lmdks, keys, newArgs, extraUnifs, efac, vars);
    } else {
      newArgs.push_back(arg);
    }
  }
  return bind::fapp(newFdecl, newArgs); // building the declaration
}

}
namespace seahorn {

Expr mkFMapKeysCore(Expr map, ExprMap &type_lambda, ExprMap &expr_type,
                    ExprFactory &efac) {

  ExprVector keys(map->args_begin(), map->args_end());
  Expr mTy = sort::finiteMapTy(keys);
  Expr lmdKeys = finite_map::mkKeys(keys, efac);

  type_lambda[mTy] = lmdKeys;
  expr_type[map] = mTy;

  return map;
}

Expr mkInitFMapCore(Expr map, ExprMap &type_lambda, ExprMap &expr_type,
                    ExprFactory &efac) {

  Expr mTy = expr_type[map->left()];
  assert(mTy);

  ExprVector keys(mTy->args_begin(), mTy->args_end());

  Expr valuesE = map->right();
  ExprVector values(valuesE->args_begin(), valuesE->args_end());

  Expr lmdKeys = type_lambda[mTy];
  assert(lmdKeys);
  Expr res = finite_map::mkInitializedMap(keys, values, efac, lmdKeys);
  expr_type[res] = mTy;

  return res;
}

Expr mkGetCore(Expr map, Expr key, ExprMap &type_lambda, ExprMap &expr_type,
               ExprSet &vars, ExprFactory &efac) {

  Expr mTy = expr_type[map];
  Expr res;

  if (bind::isFiniteMapConst(map)) { // the map is a variable
    res = mkVarGet(map, key);
    vars.insert(res); // insert new variable
  } else {               // the map is an already expanded map expression
    map = mkMapPrimitiveArgCore(map, efac);
    Expr lmdKeys = type_lambda[mTy];
    assert(lmdKeys);
    res = finite_map::mkGetVal(map, lmdKeys, key);
  }
  expr_type[res] = mTy;
  return res;
}

Expr mkSetCore(Expr map, Expr key, Expr value, ExprMap &type_lambda,
               ExprMap &expr_type, ExprSet &vars, ExprFactory &efac) {
  Expr mTy = expr_type[map];
  Expr lmd_keys = type_lambda[mTy];
  assert(lmd_keys);

  map = mkMapPrimitiveArgCore(map, efac);
  Expr res = finite_map::mkSetVal(map, lmd_keys, key, value, efac);

  expr_type[res] = mTy;
  return res;
}

Expr mkFMapConstCore(Expr map_var, ExprMap &type_lambda,
                ExprMap &expr_type, ExprFactory &efac) {

  Expr name = bind::fname(map_var);
  Expr mTy = bind::rangeTy(name);
  ExprVector keys(mTy->args_begin(), mTy->args_end());

  if (type_lambda.count(mTy) == 0) // is it necessary?, cheaper to just
                                     // overwrite with the same?
    type_lambda[mTy] = finite_map::mkKeys(keys, efac);

  expr_type[map_var] = mTy;
  return map_var;
}

Expr FiniteMapRewriter::operator()(Expr exp) {

  LOG("fmap_transf", errs() << "Rewritting " << *exp << "\n";);

  Expr res;
  if (isOpX<CONST_FINITE_MAP_KEYS>(exp)) { // defk
    res = mkFMapKeysCore(exp, m_type_lambda, m_expr_type, m_efac);
  } else if (isOpX<CONST_FINITE_MAP>(exp)) {
    res = mkInitFMapCore(exp, m_type_lambda, m_expr_type, m_efac);
  } else if (isOpX<GET>(exp)) {
    res = mkGetCore(exp->left(), exp->right(), m_type_lambda, m_expr_type, m_evars, m_efac);
  } else if (isOpX<SET>(exp)) {
    ExprVector args(exp->args_begin(), exp->args_end());
    res = mkSetCore(args[0], args[1], args[2], m_type_lambda,
                    m_expr_type, m_evars, m_efac);
  } else if (bind::isFiniteMapConst(exp)) {
    res = mkFMapConstCore(exp, m_type_lambda, m_expr_type, m_efac);
  } else if (isOpX<EQ>(exp)) {

    Expr el = exp->left();
    Expr er = exp->right();
    Expr mTy1 = m_expr_type[el];
    Expr mTy2 = m_expr_type[er];

    Expr lkeys1 = m_type_lambda[mTy1];
    Expr lkeys2 = m_type_lambda[mTy2];

    // assert(lkeys1);
    // assert(lkeys2);
    // // only one keys vector is needed, just done for compare
    ExprVector keys1(mTy1->args_begin(), mTy1->args_end());
    // ExprVector keys2(mTy2->args_begin(), mTy2->args_end());
    // assert(compare(keys1, keys2));
    // check that both maps have the same keys
    res = mkEqCore(el, lkeys1, er, lkeys2, keys1, m_efac, m_evars);
  } else { // do nothing
    assert(false && "Unexpected map expression");
    return exp;
  }
  LOG("fmap_transf",
      errs() << "Rewritten: " << *exp << "\n   to: " << *res << "\n";);
  return res;
}

  // ----------------------------------------------------------------------
  //  FiniteMapArgsVisitor
  // ----------------------------------------------------------------------

  VisitAction FiniteMapArgsVisitor::operator()(Expr exp) {

    if (isOpX<IMPL>(exp)) { // rule (or implication inside rule?)
      Expr head = exp->right();
      Expr body = exp->left();
      Expr fdecl = *head->args_begin();

      if (m_pred_decl_t.count(fdecl) == 0)
        return VisitAction::changeDoKids(exp);

      Expr newPredDecl = m_pred_decl_t.find(fdecl)->second;
      ExprVector newUnifs;
      Expr newFapp = mkFappArgs(head, newPredDecl, m_evars, m_efac, newUnifs);
      Expr newExp = boolop::limp(mk<AND>(mknary<AND>(newUnifs), body), newFapp);

      // efficiency: are we traversing the newly created unifs?
      return VisitAction::changeDoKids(newExp);

    } else if (isOpX<FAPP>(exp) &&
               !bind::isConst(exp)) { // faster to check arity >= 2?
      Expr fdecl = *exp->args_begin();

      if (m_pred_decl_t.count(fdecl) > 0) { // needs to be transformed
        ExprVector newUnifs;
        Expr newPredDecl = m_pred_decl_t.find(fdecl)->second;
        Expr newFapp =
            mkFappArgs(exp, newPredDecl, m_evars, m_efac, newUnifs);
        Expr newExp = mk<AND>(mknary<AND>(newUnifs), newFapp);
        LOG("fmap_transf", errs() << *newExp << "\n";);
        return VisitAction::changeDoKids(newExp);
      }
    } else if (isOpX<FDECL>(exp)){
      return VisitAction::skipKids();
    }
    return VisitAction::doKids();
  }

  // ----------------------------------------------------------------------
  //  FiniteMapBodyVisitor
  // ----------------------------------------------------------------------

  bool returnsFiniteMap(Expr e) {
    return isOpX<CONST_FINITE_MAP>(e) || isOpX<SET>(e) ||
           bind::isFiniteMapConst(e);
  }

  VisitAction FiniteMapBodyVisitor::operator()(Expr exp) {
    LOG("fmap_transf", errs()
                           << "Creating visit action for: " << *exp << "\n";);

    if (isFiniteMapOp(exp)) {
      return VisitAction::changeDoKidsRewrite(exp, m_rw);
    } else if (bind::isFiniteMapConst(exp)) {
      return VisitAction::changeDoKidsRewrite(exp, m_rw);
    } else if (isOpX<EQ>(exp)) {
      if (returnsFiniteMap(exp->left()) || returnsFiniteMap(exp->right()))
        return VisitAction::changeDoKidsRewrite(exp, m_rw);
    } else if (bind::isConst(exp) || bind::isFdecl(exp)) {
      return VisitAction::skipKids();
    }
    // This step doesn't need to be rewritten but the kids do
    return VisitAction::doKids();
  }

} // namespace seahorn
