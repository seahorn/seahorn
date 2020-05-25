#include "seahorn/FiniteMapTransf.hh"

#include "seahorn/Expr/ExprOpBind.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprVisitor.hh"

#include "seahorn/Support/SeaDebug.h"

using namespace expr;
using namespace expr::op;

namespace {
Expr mkVarGet(Expr map, Expr k, Expr vTy) {
  // -- create a constant with the name get(map,k)
  return bind::mkConst(variant::variant(0,finite_map::get(map, k)), vTy);
}

// \brief `m1` contains the same values as `m2`. Both maps are assumed to have
// the same keys `keys` but not necessarily in the same order, that is why
// `ks1` and `ks2` are needed.
Expr mkEqCore(Expr m1, Expr ks1, Expr m2, Expr ks2, ExprVector &keys, Expr vTy,
              ExprFactory &efac, ExprSet &evars) {

  ExprVector conj;

  bool is_var_m1 = bind::isFiniteMapConst(m1);
  bool is_var_m2 = bind::isFiniteMapConst(m2);

  Expr e_m1, e_m2;

  for (auto k : keys) {
    if (is_var_m1) {
      e_m1 = mkVarGet(m1, k, vTy);
      evars.insert(e_m1);
    } else
      e_m1 = finite_map::mkGetVal(m1, ks1, k);

    if (is_var_m2) {
      e_m2 = mkVarGet(m2, k, vTy);
      evars.insert(e_m2);
    } else
      e_m2 = finite_map::mkGetVal(m2, ks2, k);
    conj.push_back(mk<EQ>(e_m1, e_m2));
  }
  return mknary<AND>(conj);
}

Expr mkInitFMapCore(Expr map, ExprMap &type_lambda, ExprMap &expr_type,
                    ExprFactory &efac) {

  // defmap(defk(keys), default(valTy)))
  //      or
  // defmap(defk(keys), defv(values)))

  // build keys
  Expr defk = map->left();
  assert(isOpX<CONST_FINITE_MAP_KEYS>(defk));
  ExprVector keys(defk->args_begin(), defk->args_end());

  Expr vTy, valuesE = map->right();
  if (isOpX<FINITE_MAP_VAL_DEFAULT>(valuesE)) { // non init values
    vTy = valuesE->left();                      // type of the values
  } else {
    assert(isOpX<CONST_FINITE_MAP_VALUES>(valuesE)); // initialized values
    vTy = bind::typeOf(*valuesE->args_begin());
    // already expanded, can they be of unknown type?
  }

  Expr fmTy = sort::finiteMapTy(vTy, keys);
  expr_type[map] = fmTy;
  Expr lmdKeys = finite_map::mkKeys(keys, efac);
  type_lambda[fmTy] = lmdKeys;

  return map;
}

  Expr mkFMapPrimitiveArgCore(Expr map, ExprMap &type_lambda,
                              ExprMap &expr_type, ExprFactory &efac) {

    if (isOpX<CONST_FINITE_MAP>(map)){
      Expr defk = map->left();
      assert(isOpX<CONST_FINITE_MAP_KEYS>(defk));
      Expr lmdKeys = type_lambda[map];
      Expr fmTy = expr_type[map];
      Expr res, valuesE = map->right();
      Expr vTy = finite_map::valTy(fmTy);
      if (isOpX<FINITE_MAP_VAL_DEFAULT>(valuesE)) { // non init values
        return finite_map::mkEmptyMap(vTy, efac);
      } else {
        assert(isOpX<CONST_FINITE_MAP_VALUES>(valuesE)); // initialized values
        ExprVector values(valuesE->args_begin(), valuesE->args_end());
        ExprVector keys(defk->args_begin(), defk->args_end());
        return finite_map::mkInitializedMap(keys, vTy, values, efac, lmdKeys);
      }
    }
    else // already transformed map: 0 or ite expr
      return map;
  }

  // \brief expands a map into separate scalar variables
  void mkVarsMap(Expr map, Expr lmdks, ExprVector &keys, Expr vTy,
                 ExprVector &new_vars, ExprVector &extra_unifs,
                 ExprFactory &efac, ExprSet &evars) {

    Expr v, v_get;
    ExprVector map_values(keys.size());
    auto val_it = map_values.begin();

    for (auto k : keys) {
      v = mkVarGet(map, k, vTy);
      evars.insert(v);
      new_vars.push_back(k);
      new_vars.push_back(v);
      *val_it++ = v;
    }
    extra_unifs.push_back(
        mk<EQ>(map, finite_map::constFiniteMap(keys, map_values)));
  }

  // \brief expands the map arguments of fapps into separate scalar variables
  Expr mkFappArgsCore(Expr fapp, Expr newFdecl, ExprSet &vars, ExprFactory &efac,
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

      if (isOpX<FINITE_MAP_TY>(argTy)) {
        Expr map_var_name;
        if (bind::isFiniteMapConst(arg)) {
          map_var_name = arg;
        } else {
          map_var_name = variant::variant(arg_count, fname);
          // if there is no name, we create a variant with the name of the
          // function, make new variable (same as normalization)
        }
        Expr ksTy = finite_map::keys(argTy);
        ExprVector keys(ksTy->args_begin(), ksTy->args_end());
        Expr lmdks = finite_map::mkKeys(keys, efac);

        mkVarsMap(map_var_name, lmdks, keys, finite_map::valTy(argTy), newArgs,
                  extraUnifs, efac, vars);
        // new arguments are added to `newArgs` in the function above
      } else {
        newArgs.push_back(arg);
      }
    }
    return bind::fapp(newFdecl, newArgs); // building the new fapp
  }

Expr mkGetCore(Expr map, Expr key, ExprMap &type_lambda, ExprMap &expr_type,
               ExprSet &vars, ExprFactory &efac) {

  Expr fmTy = expr_type[map];
  Expr res;

  if (bind::isFiniteMapConst(map)) { // the map is a variable
    res = mkVarGet(map, key, finite_map::valTy(fmTy));
    vars.insert(res); // insert new variable
  } else {
    map = mkFMapPrimitiveArgCore(map, type_lambda, expr_type, efac);
    Expr lmdKeys = type_lambda[fmTy];
    assert(lmdKeys);
    res = finite_map::mkGetVal(map, lmdKeys, key);
  }
  return res;
}

Expr mkSetCore(Expr map, Expr key, Expr value, ExprMap &type_lambda,
               ExprMap &expr_type, ExprSet &vars, ExprFactory &efac) {
  Expr fmTy = expr_type[map];
  Expr vTy = finite_map::valTy(fmTy);
  Expr ksTy = finite_map::keys(fmTy);
  Expr lmdKeys = type_lambda[fmTy];
  assert(lmdKeys);

  ExprVector extraUnifs;
  if(bind::isFiniteMapConst(map)){
    ExprVector keys(ksTy->args_begin(), ksTy->args_end());
    ExprVector values;
    for(auto k : keys){
      Expr v = mkVarGet(map, k, vTy);
      vars.insert(v);
      values.push_back(v);
    }
    map = finite_map::mkInitializedMap(keys, vTy, values, efac, lmdKeys);
  } else
    map = mkFMapPrimitiveArgCore(map, type_lambda, expr_type, efac);

  Expr res = finite_map::mkSetVal(map, lmdKeys, key, value, efac);

  expr_type[res] = fmTy;
  return res;
}

Expr mkFMapConstCore(Expr map_var, ExprMap &type_lambda,
                     ExprMap &expr_type, ExprFactory &efac) {

  if (expr_type.count(map_var) == 0) {
    Expr fmTy = bind::rangeTy(bind::fname(map_var));
    Expr ksTy = finite_map::keys(fmTy);
    ExprVector keys(ksTy->args_begin(), ksTy->args_end());
    type_lambda[fmTy] = finite_map::mkKeys(keys, efac);
    expr_type[map_var] = fmTy;
  }
  return map_var;
}
}

namespace seahorn {

Expr FiniteMapRewriter::operator()(Expr exp) {

  Expr res;

  if (isOpX<CONST_FINITE_MAP>(exp)) {
    res = mkInitFMapCore(exp, m_type_lambda, m_expr_type, m_efac);
  } else if (isOpX<GET>(exp)) {
    res = mkGetCore(exp->left(), exp->right(), m_type_lambda, m_expr_type,
                    m_evars, m_efac);
  } else if (isOpX<SET>(exp)) {
    ExprVector args(exp->args_begin(), exp->args_end());
    res = mkSetCore(args[0], args[1], args[2], m_type_lambda,
                    m_expr_type, m_evars, m_efac);
  } else if (bind::isFiniteMapConst(exp)) {
    res = mkFMapConstCore(exp, m_type_lambda, m_expr_type, m_efac);
  } else if (isOpX<EQ>(exp)) {

    Expr fml =
        mkFMapPrimitiveArgCore(exp->left(), m_type_lambda, m_expr_type, m_efac);
    Expr fmr =
        mkFMapPrimitiveArgCore(exp->right(), m_type_lambda, m_expr_type, m_efac);
    Expr fmTyl = m_expr_type[fml];
    Expr fmTyr = m_expr_type[fmr];

    Expr lkeysl = m_type_lambda[fmTyl];
    Expr lkeysr = m_type_lambda[fmTyr];

    Expr ksTyl = finite_map::keys(fmTyl);
    Expr vTy = finite_map::valTy(fmTyl);
    ExprVector keys(ksTyl->args_begin(), ksTyl->args_end());
    res = mkEqCore(fml, lkeysl, fmr, lkeysr, keys, vTy, m_efac, m_evars);
  } else { // do nothing
    assert(false && "Unexpected map expression");
    return exp;
  }
  LOG("fmap_transf", errs() << "Rewritten: " << *exp << "\n   to: " << *res << "\n";);
  return res;
}

// ----------------------------------------------------------------------
//  FiniteMapArgsVisitor
// ----------------------------------------------------------------------

VisitAction FiniteMapArgsVisitor::operator()(Expr exp) {

  if (isOpX<IMPL>(exp)) { // rule (or implication inside rule?)
    Expr head = exp->right();
    Expr body = exp->left();
    assert(body); // facts!
    Expr fdecl = *head->args_begin();

    if (m_pred_decl_t.count(fdecl) == 0)
      return VisitAction::changeDoKids(exp);

    Expr newPredDecl = m_pred_decl_t.find(fdecl)->second;
    ExprVector newUnifs;
    Expr newFapp = mkFappArgsCore(head, newPredDecl, m_evars, m_efac, newUnifs);
    Expr newBody = newUnifs.empty() ? body : mk<AND>(mknary<AND>(newUnifs), body);

    Expr newExp = boolop::limp(newBody, newFapp);
    // efficiency: are we traversing the newly created unifs?
    return VisitAction::changeDoKids(newExp);

  } else if (isOpX<FAPP>(exp) &&
             !bind::IsConst()(exp)) { // faster to check arity >= 2?
    Expr fdecl = *exp->args_begin();
    if (m_pred_decl_t.count(fdecl) > 0) { // needs to be transformed
      ExprVector newUnifs;
      Expr newPredDecl = m_pred_decl_t.find(fdecl)->second;
      Expr newExp = mkFappArgsCore(exp, newPredDecl, m_evars, m_efac, newUnifs);
      if (!newUnifs.empty())
        newExp = mk<AND>(mknary<AND>(newUnifs), newExp);
      LOG("fmap_transf", errs() << *newExp << "\n";);
      return VisitAction::changeDoKids(newExp);
    }
  } else if (isOpX<FDECL>(exp)) {
    return VisitAction::skipKids();
  }
  return VisitAction::doKids();
}

// ----------------------------------------------------------------------
//  FiniteMapBodyVisitor
// ----------------------------------------------------------------------

static bool returnsFiniteMap(Expr e) {
  return isOpX<CONST_FINITE_MAP>(e) || isOpX<SET>(e) ||
         bind::isFiniteMapConst(e);
}

VisitAction FiniteMapBodyVisitor::operator()(Expr exp) {
  LOG("fmap_transf", errs() << "Creating visit action for: " << *exp << "\n";);

  if (isVisitFiniteMapOp(exp)) {
    return VisitAction::changeDoKidsRewrite(exp, m_rw);
    } else if (bind::isFiniteMapConst(exp)) {
      return VisitAction::changeDoKidsRewrite(exp, m_rw);
    } else if (isOpX<EQ>(exp)) {
      if (returnsFiniteMap(exp->left()) || returnsFiniteMap(exp->right()))
        return VisitAction::changeDoKidsRewrite(exp, m_rw);
  } else if (bind::IsConst()(exp) || bind::isFdecl(exp)) {
      return VisitAction::skipKids();
    }
    // The step doesn't need to be rewritten but the kids do
    return VisitAction::doKids();
  }

bool FiniteMapBodyVisitor::isVisitFiniteMapOp(Expr e) {
    return isOpX<CONST_FINITE_MAP>(e) || isOpX<GET>(e) || isOpX<SET>(e);
    // we are not visiting CONST_FINITE_MAP_KEYS, DEFAULT,
  }

} // namespace seahorn

