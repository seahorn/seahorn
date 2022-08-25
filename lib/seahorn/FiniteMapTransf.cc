#include "seahorn/FiniteMapTransf.hh"

#include "seahorn/Expr/ExprOpBind.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"

using namespace expr;
using namespace expr::op;

namespace seahorn {
bool FmapsNegCond;
InterMemFMStats g_imfm_stats;

// ----------------------------------------------------------------------
//  FiniteMapArgsVisitor
// ----------------------------------------------------------------------

// \brief rewrites a map into separate scalar variables. New arguments are added
// to `newArgs`, new unifications are added to `extra_unifs`
template <typename Range>
void mkVarsMap(Expr mapConst, Expr map, const Range &keys, int nKs, Expr kTy,
               Expr vTy, ExprVector::iterator &newArg_it,
               ExprVector &extra_unifs, ExprSet &evars) {

  Expr v, key;

  if (nKs == 1) {
    v = fmap::mkVarGet(mapConst, *keys.begin(), 0, vTy);
    evars.insert(v);
    *newArg_it++ = v;
  } else
    for (auto k : keys) {
      key = fmap::mkVarKey(mapConst, k, kTy);
      v = fmap::mkVarGet(mapConst, k, 0, vTy);
      evars.insert(v);
      evars.insert(key);
      *newArg_it++ = key;
      *newArg_it++ = v;
    }
}

// \brief rewrites the map arguments of fapps into separate scalar variables
static Expr mkFappArgsCore(Expr fapp, Expr newFdecl, ExprVector &extraUnifs,
                           ExprSet &evars, ExprFactory &efac) {

  assert(isOpX<FAPP>(fapp));

  Expr fdecl = bind::name(fapp);
  assert(bind::isFdecl(fdecl));
  Expr fname = bind::fname(fdecl);

  ExprVector newArgs(newFdecl->arity() - 2); // 2: fname, ret

  auto arg_it = ++(fapp->begin()), t_it = ++(fdecl->begin());
  auto nArg_it = newArgs.begin();

  int arg_count = 0;
  for (; arg_it != fapp->end(); arg_it++, arg_count++, t_it++) {
    Expr arg = *arg_it;
    Expr argTy = *t_it;

    if (isOpX<FINITE_MAP_TY>(argTy)) {
      unsigned nKs = sort::finiteMapKeyTy(argTy)->arity();

      if (bind::isFiniteMapConst(arg)) {
        // generated when the node is bounded but not live
        evars.erase(arg);
        Expr ksTy = sort::finiteMapKeyTy(bind::rangeTy(bind::fname(arg)));
        // the keys are obtained from the const, not the type. The Dsa info
        // of the type is relative to the function (context insensitive), the
        // Dsa info on the type of the const is relative to the calling
        // context.
        auto keys = llvm::make_range(ksTy->begin(), ksTy->end());

        mkVarsMap(arg, arg, keys, nKs, bind::rangeTy(bind::fname(ksTy->arg(0))),
                  sort::finiteMapValTy(argTy), nArg_it, extraUnifs, evars);
        // new arguments are added to `newArgs` in the function above
      } else {
        Expr fmd = fmap_transf::expandToVal(arg);

        if (nKs == 1)
          *nArg_it++ = fmap::fmapValValues(fmd)->first();
        else {
          Expr ks = fmap::fmapValKeys(fmd);
          auto v_it = fmap::fmapValValues(fmd)->begin();
          for (auto k_it = ks->begin(); k_it != ks->end(); k_it++, v_it++) {
            *nArg_it++ = *k_it;
            *nArg_it++ = *v_it;
          }
        }
      }
    } else {
      assert(!bind::isFiniteMapConst(arg));
      *nArg_it++ = arg;
    }
  }
  return bind::fapp(newFdecl, newArgs); // building the new fapp
}

Expr FiniteMapArgRewriter::operator()(Expr exp) {

  if (isOpX<IMPL>(exp)) { // rule (or implication inside rule?)
    Expr head = exp->right();
    Expr fdecl = head->first();

    ExprVector newUnifs;
    Expr newFapp = mkFappArgsCore(head, m_pred_decl_t.find(fdecl)->second,
                                  newUnifs, m_evars, m_efac);

    Expr body = exp->left();
    Expr newBody =
        newUnifs.empty() ? body : boolop::land(body, boolop::land(newUnifs));

    return boolop::limp(newBody, newFapp);
  } else if (isOpX<FAPP>(exp)) {
    ExprVector newUnifs;
    Expr newExp =
        mkFappArgsCore(exp, m_pred_decl_t.find(bind::name(exp))->second,
                       newUnifs, m_evars, m_efac);
    newUnifs.push_back(newExp);
    return boolop::land(newUnifs);
  }
  return exp;
}

// rewrite bottom_up
VisitAction FiniteMapArgsVisitor::operator()(Expr exp) {

  if (isOpX<IMPL>(exp) && bind::isFapp(exp->right()) &&
      m_pred_decl_t.count(exp->right()->first()) >
          0) // rule (or implication inside rule?)
    return VisitAction::changeDoKids((*m_rw)(exp));
  else if (bind::IsConst()(exp) ||
           bind::isFdecl(exp)) // TODO: more cases to skip?
    return VisitAction::skipKids();
  else if (bind::isFapp(exp) && m_pred_decl_t.count(bind::name(exp)) > 0)
    return VisitAction::changeDoKidsRewrite(exp, m_rw);

  return VisitAction::doKids();
}

} // namespace seahorn

namespace {

using namespace seahorn;

// ----------------------------------------------------------------------
//  Ite dsa-based top-down simplifier
// ----------------------------------------------------------------------

static Expr getCellExprVariant(Expr e) {
  assert(bind::IsConst()(e));

  // assumes only 1 level of variance
  Expr name = variant::mainVariant(bind::name(bind::fname(e)));
  Expr cellE = variant::getTag(name);

  if (!isOpX<CELL>(cellE)) // cell tags are included inside the key tag
    cellE = variant::getTag(bind::name(bind::fname(cellE)));

  assert(isOpX<CELL>(cellE));
  return cellE; // cell id
}

static Expr getCellExpr(Expr e) {

  // only supporting one level of +
  if (isOpX<PLUS>(e))
    e = e->left();

  return getCellExprVariant(e);
}

static unsigned getOffsetCellExpr(Expr e) {

  unsigned offset = 0;

  // only supporting one level of +
  if (isOpX<PLUS>(e)) {
    mpz_class o = getTerm<mpz_class>(e->right());
    offset += o.get_ui(); // TODO: overflow? dangerous?
    e = e->left();
  }

  e = getCellExprVariant(e);

  assert(isOpX<CELL>(e));
  return offset + getTerm<unsigned>(e->right());
}

// for debugging
static bool sameNode(Expr e1, Expr e2) {
  return getCellExpr(e1)->left() == getCellExpr(e2)->left();
}

static bool validDsaConst(Expr e) {
  if (!bind::IsConst()(e))
    return false;

  Expr name = variant::mainVariant(bind::name(bind::fname(e)));
  if (name == nullptr)
    return false;
  Expr cellE = variant::getTag(name);
  if (cellE == nullptr)
    return false;

  if (isOpX<CELL>(cellE))
    return true;
  else if (bind::fname(cellE) != nullptr) {
    Expr name = bind::name(bind::fname(cellE));
    cellE = variant::getTag(name);
    return cellE != nullptr && isOpX<CELL>(cellE);
  }
  return false;
}

static bool evaluableDsaExpr(Expr e) {
  if (validDsaConst(e))
    return true;

  return isOpX<PLUS>(e) && validDsaConst(e->left()) && isOp<MPZ>(e->right());
}

static Expr evalCondDsa(Expr cond) {

  Expr lhs = cond->left(), rhs = cond->right();
  if (lhs == rhs)
    return mk<TRUE>(cond->efac());
  else if (isOp<MPZ>(lhs) && isOp<MPZ>(rhs) && lhs != rhs)
    return mk<FALSE>(cond->efac()); // if they are different integers
  else if (!evaluableDsaExpr(lhs) || !evaluableDsaExpr(rhs))
    return cond;

  unsigned lo = getOffsetCellExpr(lhs);
  unsigned ro = getOffsetCellExpr(rhs);

  assert(sameNode(lhs, rhs));

  if (lo != ro) // if they encode a different cell, return false
    return mk<FALSE>(cond->efac());
  else
    return cond;
}

// dsa-based ite simplifier
class IteTopDownVisitor : public std::unary_function<Expr, VisitAction> {

  ExprFactory &m_efac;

public:
  IteTopDownVisitor(ExprFactory &efac) : m_efac(efac) {}

  VisitAction operator()(Expr exp) {
    if (isOpX<ITE>(exp) && isOpX<EQ>(exp->left())) {
      Expr cond = evalCondDsa(exp->left());
      while (isOpX<FALSE>(cond)) {
        exp = exp->last();
        if (isOpX<ITE>(exp) && isOpX<EQ>(exp->left()))
          cond = evalCondDsa(exp->left());
        else
          break;
      }
      if (isOpX<FALSE>(cond))
        return VisitAction::changeDoKids(exp);
      else
        return VisitAction::changeDoKids(
            boolop::lite(cond, exp->arg(1), exp->arg(2)));
    } else if (bind::IsConst()(exp) || bind::isFdecl(exp))
      return VisitAction::skipKids();
    else
      return VisitAction::doKids();
  }
};

static Expr dsaIteSimplify(Expr e) {
  IteTopDownVisitor itdv(e->efac());
  return visit(itdv, e);
}

// ----------------------------------------------------------------------
//  Transformation of operations over fmap values
// ----------------------------------------------------------------------

// -- obtains a value from a fmap value
static Expr mkGetValCore(Expr fmv, Expr key) {

  Expr ks = fmap::fmapValKeys(fmv);
  Expr vs = fmap::fmapValValues(fmv);

  if (ks->arity() == 1)
    return vs->left();

  std::vector<unsigned> matches;
  ExprVector conds;
  auto k_it = ks->begin();
  for (unsigned i = 0; i < ks->arity(); i++, k_it++) { // find keys that match
    Expr cond = evalCondDsa(mk<EQ>(*k_it, key));
    if (!isOpX<FALSE>(cond)) {
      matches.push_back(i);
      conds.push_back(cond);
      if (isOpX<TRUE>(cond))
        break; // stop search, but keep the previous matches
    }
  }

  if (matches.empty()) // if no keys match, return last value
    return vs->last();

  LOG("inter_mem_counters", g_imfm_stats.newAlias(matches.size()););
  if (matches.size() == 1)
    return vs->arg(matches[0]);

  auto m_it = matches.rbegin(); // reverse iterator
  Expr ite = vs->arg(*m_it);
  m_it++;
  // construct ite for the keys that match
  for (auto c_it = ++conds.rbegin(); m_it != matches.rend(); m_it++, c_it++)
    ite = fmap_transf::mkFMIte(*c_it, vs->arg(*m_it), ite);

  return ite;
}

static template <typename Range>
Expr replaceValues(Expr fmv, const Range &values) {
  return fmap::constFiniteMap(fmap::fmapValKeys(fmv), fmap::fmapValDefault(fmv),
                              fmap::constFiniteMapValues(values));
}

// -- obtains a new definition after inserting a value, returns `nullptr` if the
// -- value could be placed in several keys
static Expr mkSetValCore(Expr fmv, Expr key, Expr v) {

  Expr vs = fmap::fmapValValues(fmv);

  LOG("inter_mem_counters", g_imfm_stats.newSize(vs->arity()););

  if (vs->arity() == 1) { // fmap of size 1
    ExprVector value = {v};
    return replaceValues(fmv, value);
  }

  std::vector<unsigned> matches;
  ExprVector conds;
  Expr ks = fmap::fmapValKeys(fmv);
  auto k_it = ks->begin();
  for (int i = 0; i < ks->arity(); i++, k_it++) { // find keys that match
    Expr cond = evalCondDsa(mk<EQ>(*k_it, key));
    if (!isOpX<FALSE>(cond)) {
      matches.push_back(i);
      conds.push_back(cond);
      if (isOpX<TRUE>(cond))
        break; // stop search, but keep the previous matches
    }
  }

  // if no keys match, return last value
  if (matches.empty()) // this should not happen, return def as it is?
    matches.push_back(ks->arity() - 1);

  ExprVector nvalues(ks->arity());
  auto ov_it = vs->begin();
  if (matches.size() == 1) { // replace the value of the only matched key
    int nextCh = matches[0];
    for (int i = 0; i < ks->arity(); i++, ov_it++)
      if (i == nextCh)
        nvalues[i] = v;
      else
        nvalues[i] = *ov_it;
  } else {
    LOG("inter_mem_counters", g_imfm_stats.newAlias(matches.size()););
    int mit = 0;
    int nextCh = matches[0];
    for (int i = 0; i < ks->arity(); i++, ov_it++) {
      if ((mit < matches.size()) && (i == nextCh)) {
        nvalues[i] = fmap_transf::mkFMIte(conds[mit], v, *ov_it);
        nextCh = matches[++mit];
      } else
        nvalues[i] = *ov_it;
    }
  }

  return replaceValues(fmv, nvalues);
}

static Expr mkIteValCore(Expr cond, Expr fmv1, Expr fmv2) {

  ExprVector nvs(fmap::fmapValKeys(fmv1)->arity());

  auto vs1_it = fmap::fmapValValues(fmv1)->begin();
  auto vs2_it = fmap::fmapValValues(fmv2)->begin();

  for (auto nvs_it = nvs.begin(); nvs_it != nvs.end(); nvs_it++)
    *nvs_it = mk<ITE>(cond, *vs1_it++, *vs2_it++);

  return replaceValues(fmv1, nvs);
  // TODO: add side condition that the keys are the same?
}

// ----------------------------------------------------------------------
//  FiniteMapBodyVisitor
// ----------------------------------------------------------------------

// -- rewrites a map term (if not already) to be used in a map primitive
static Expr mkFMapPrimitiveArgCore(Expr map, FMapExprsInfo &fmei) {

  Expr kTy;
  Expr mapTransf = map;

  if (bind::isFiniteMapConst(map)) {
    // if the map is a variable, it is assumed to be defined or expanded
    // before.
    assert((fmei.m_fmapVarTransf.count(map) > 0) && "no fmap val found");
    Expr fmTy = fmei.m_type[map];
    assert(fmTy);
    kTy = bind::rangeTy(bind::name(sort::finiteMapKeyTy(fmTy)->arg(0)));
    mapTransf = fmei.m_fmapVarTransf[map];
  }

  if (fmap::isFmapVal(mapTransf)) {
    // the map is a map definition
    Expr ks = fmap::fmapValKeys(mapTransf);
    kTy = bind::typeOf(ks->left());
    Expr valuesE = fmap::fmapValValues(mapTransf);
    return fmap::mkFMapVal(llvm::make_range(ks->begin(), ks->end()), kTy,
                           llvm::make_range(valuesE->begin(), valuesE->end()),
                           fmap::fmapValDefault(mapTransf)->first());

  } else // already transformed map: default-map or ite expr
    return mapTransf;
}

static Expr getValueAtVal(Expr map, Expr k, unsigned pos,
                          ZSimplifier<EZ3> &zsimp) {
  if (fmap::isFmapVal(map)) {
    if (fmap::isFmapVal(map))
      return fmap::fmapValValues(map)->arg(pos);
    else
      return fmap::fmapValDefault(map)->left();
  } // already an expanded map term

  return zsimp.simplify(
      dsaIteSimplify(fmap::get(map, k))); // TODO: remove basic simplifier?
}

// \brief `ml` contains the same values as `mr`.
static Expr mkEqCoreBody(Expr ml, Expr mr, FMapExprsInfo &fmei) {

  LOG("fmap_transf", errs() << "-- mkEqCore " << *ml << " = " << *mr << "\n";);
  Expr mrValk, mlValk;

  if (!fmap::isFmapVal(mr)) {
    if (bind::isFiniteMapConst(mr)) { // if variable, use its expansion
      if (fmei.m_fmapKeys.count(mr) == 0) {
        assert(false && "undefined fmap");
        return mk<EQ>(ml, mr);
      } else { // already expanded const
        mrValk = fmei.m_fmapKeys[mr];
        mr = fmei.m_fmapVarTransf[mr];
      }
    } else // already expanded expression
      mrValk = fmei.m_fmapKeys[mr];
  } else
    mrValk = fmap::fmapValKeys(mr);

  assert(mrValk && isOpX<CONST_FINITE_MAP_KEYS>(mrValk));

  if (bind::isFiniteMapConst(ml)) {
    if (fmei.m_fmapVarTransf.count(ml) == 0) { // first appearance of the const
      // reduce to true equalities when the left hand side is a variable and
      // it appeared for the first time, to use the right hand side whenever
      // the left variable appears store map definition and transform to true
      //
      // this optimization can only be done if they are in the same scope
      if (fmei.m_dimpl != 0) {
        assert(false && "equality inside of an implication not allowed");
        return mk<EQ>(ml, mr);
      }
      fmei.m_fmapKeys[ml] = mrValk;
      fmei.m_type[ml] = fmei.m_type[mr];
      fmei.m_fmapVarTransf[ml] = mr;
      return mk<TRUE>(fmei.m_efac);
    } else {
      mlValk = fmei.m_fmapKeys[ml];
      ml = fmei.m_fmapVarTransf[ml];
    }
  } else
    mlValk = fmei.m_fmapKeys[ml];

  assert(mlValk && isOpX<CONST_FINITE_MAP_KEYS>(mlValk));

  bool skipKs = (mlValk == mrValk) || (mlValk->arity() == 1);
  bool skipVs = (ml == mr);

  if (skipKs &&
      skipVs) // skip this if it is the same expansion of keys and values
    return mk<TRUE>(fmei.m_efac);

  ExprVector conj;
  auto l_it = mlValk->begin();
  auto r_it = mrValk->begin();

  for (int i = 0; l_it != mlValk->end(); i++, l_it++, r_it++) {
    // unify keys (from the definition)
    assert(r_it != mrValk->end() && "maps with a different number of keys");

    if (!skipKs && *l_it != *r_it)
      conj.push_back(mk<EQ>(*l_it, *r_it));

    if (!skipVs) { // unify values
      Expr vl = getValueAtVal(ml, mlValk->arg(i), i, fmei.m_zsimp);
      Expr vr = getValueAtVal(mr, mrValk->arg(i), i, fmei.m_zsimp);
      if (vl != vr)
        conj.push_back(mk<EQ>(vl, vr));
    }
  }

  return conj.empty() ? mk<TRUE>(fmei.m_efac) : boolop::land(conj);
}

// -- processes a fmap value, building the type and the lmdkeys
// term is of the form:
// defmap(ks(keys), fmap-default(defval), defv(values)))
static Expr mkValFMapCoreBody(Expr map, FMapExprsInfo &fmei) {

  Expr ks = fmap::fmapValKeys(map);
  Expr vTy = bind::typeOf(fmap::fmapValDefault(map)->left());

  auto keys = llvm::make_range(ks->begin(), ks->end());
  fmei.m_type[map] = sort::finiteMapTy(vTy, keys);

  return map;
}

static Expr mkGetCoreBody(Expr map, Expr key, FMapExprsInfo &fmei) {

  LOG("fmap_transf", errs() << "-- mkGetCore " << *map << " " << *key << "\n";);

  Expr fmv = map;

  if (bind::isFiniteMapConst(map)) {
    if (fmei.m_type.count(map) == 0) {
      assert(false && "map definition not found");
      return fmap::get(map, key);
    }
    fmv = fmei.m_fmapVarTransf[map];
  }

  // get from fmap val
  if (fmap::isFmapVal(fmv))
    return mkGetValCore(fmv, key);

  // get from lambda
  map = mkFMapPrimitiveArgCore(map, fmei);
  // does eager simplification during beta reduction
  return dsaIteSimplify(fmei.m_zsimp.simplify(fmap::get(map, key)));
}

// -- rewrites a map set primitive
static Expr mkSetCoreBody(Expr map, Expr key, Expr v, FMapExprsInfo &fmei) {

  LOG("fmap_transf",
      errs() << "-- mkSetCore " << *map << " " << *key << " " << *v << "\n";);

  Expr fmv = map;
  if (bind::isFiniteMapConst(map))
    fmv = fmei.m_fmapVarTransf[map];

  if (fmap::isFmapVal(fmv)) {
    fmv = mkSetValCore(fmv, key, v);
    if (fmv != nullptr)
      return fmv;
  }
  Expr procMap = mkFMapPrimitiveArgCore(map, fmei);

  Expr fmTy = fmei.m_type[map];
  Expr kTy = bind::rangeTy(bind::name(sort::finiteMapKeyTy(fmTy)->arg(0)));

  Expr ks =
      fmap::isFmapVal(map) ? fmap::fmapValKeys(map) : fmei.m_fmapKeys[map];
  Expr res = fmap::set(procMap, key, v);

  fmei.m_fmapKeys[res] = ks;
  fmei.m_type[res] = fmTy;

  return res;
}

static Expr getValFmapConst(Expr m, FMapExprsInfo &fmei) {
  if (fmei.m_fmapKeys.count(m) == 0)
    return fmap::fmapValKeys(fmap::mkVal(m, 0));
  else
    return fmei.m_fmapKeys[m];
}

static Expr mkSameKeysCore(Expr lmap, Expr er, FMapExprsInfo &fmei) {

  Expr lhs = getValFmapConst(lmap, fmei);
  Expr rhs = bind::isFiniteMapConst(er) ? getValFmapConst(er, fmei) : er;
  assert(lhs->arity() == rhs->arity());

  ExprVector conj(lhs->arity());
  auto c_it = conj.begin();
  auto l_it = lhs->begin();
  auto r_it = rhs->begin();
  for (; l_it != lhs->end(); c_it++, l_it++, r_it++)
    *c_it = mk<EQ>(*l_it, *r_it);

  return boolop::land(conj);
}

static Expr mkIteCoreBody(Expr ite, FMapExprsInfo &fmei) {
  Expr th = ite->arg(1);
  Expr el = ite->last();

  /// -- we can use the `th` or the `el`
  Expr thKeys = fmei.m_fmapKeys[th];

  Expr ty = fmei.m_type[th];

  th = mkFMapPrimitiveArgCore(th, fmei);
  el = mkFMapPrimitiveArgCore(el, fmei);

  Expr x = bind::mkConst(mkTerm<std::string>("x", fmei.m_efac),
                         bind::rangeTy(bind::fname(thKeys->arg(0))));
  Expr res =
      bind::abs<LAMBDA>(std::array<Expr, 1>{x},
                        boolop::lite(ite->first(), bind::betaReduce(th, x),
                                     bind::betaReduce(el, x)));
  fmei.m_fmapKeys[res] = thKeys;
  fmei.m_type[res] = ty;

  return res;
}

class FMRewritter : public std::unary_function<Expr, Expr> {
  ExprMap &m_fmv;

public:
  FMRewritter(ExprMap &fmv) : m_fmv(fmv){};
  Expr operator()(Expr exp) {
    Expr fm = exp->left();
    Expr val = bind::isFiniteMapConst(fm) ? m_fmv[fm] : fm;
    assert(fmap::isFmapVal(val));

    return mkGetValCore(val, exp->right());
  }
};

// -- inlines values in a definition bottom-up (resolving get operations)
class FMVisitor : public std::unary_function<Expr, VisitAction> {
  std::shared_ptr<FMRewritter> m_rw;

public:
  FMVisitor(ExprMap &valmap) { m_rw = std::make_shared<FMRewritter>(valmap); };

  VisitAction operator()(Expr exp) {
    if (isOpX<GET>(exp))
      return VisitAction::changeDoKidsRewrite(exp, m_rw);
    else if (bind::IsConst()(exp))
      return VisitAction::skipKids();

    return VisitAction::doKids();
  }
};

} // namespace

namespace seahorn {

Expr FiniteMapBodyRewriter::operator()(Expr exp) {

  Expr res;

  if (fmap::isFmapVal(exp)) {
    res = mkValFMapCoreBody(exp, m_fmei);
  } else if (isOpX<GET>(exp)) {
    res = mkGetCoreBody(exp->left(), exp->right(), m_fmei);
  } else if (isOpX<SET>(exp)) {
    res = mkSetCoreBody(exp->arg(0), exp->arg(1), exp->arg(2), m_fmei);
  } else if (isOpX<ITE>(exp)) {
    res = mkIteCoreBody(exp, m_fmei);
  } else if (isOpX<EQ>(exp)) {
    res = mkEqCoreBody(exp->left(), exp->right(), m_fmei);
  } else if (isOpX<IMPL>(exp)) {
    m_fmei.m_dimpl--;
    return exp;
  } else if (isOpX<SAME_KEYS>(exp)) {
    res = mkSameKeysCore(exp->left(), exp->right(), m_fmei);
  } else {
    assert(false && "Unexpected map expression");
    res = exp;
  }
  LOG("fmap_transf",
      errs() << "Rewritten: " << *exp << "\n   to: " << *res << "\n";);
  return res;
}

bool FiniteMapBodyVisitor::isRewriteFiniteMapOp(Expr e) {
  return fmap::isFmapVal(e) || isOpX<GET>(e) || isOpX<SET>(e) ||
         isOpX<SAME_KEYS>(e);
}

VisitAction FiniteMapBodyVisitor::operator()(Expr exp) {

  if (isRewriteFiniteMapOp(exp))
    return VisitAction::changeDoKidsRewrite(exp, m_rw);
  else if (isOpX<ITE>(exp) && fmap::isFiniteMap(exp->right()))
    return VisitAction::changeDoKidsRewrite(exp, m_rw);
  else if (isOpX<EQ>(exp) && fmap::isFiniteMap(exp->left()))
    return VisitAction::changeDoKidsRewrite(exp, m_rw);
  else if (bind::IsConst()(exp) || bind::isFdecl(exp))
    return VisitAction::skipKids();
  else if (isOpX<IMPL>(exp)) {
    m_dimpl++;
    // no rewritting necessary but we need to mark that we exited it
    return VisitAction::changeDoKidsRewrite(exp, m_rw);
  }

  return VisitAction::doKids();
}

Expr rewriteFiniteMapArgs(Expr e, const ExprMap &predDeclMap) {
  ExprSet evars;
  return rewriteFiniteMapArgs(e, evars, predDeclMap);
}

Expr rewriteFiniteMapArgs(Expr e, ExprSet &evars, const ExprMap &predDeclMap) {
  DagVisitCache dvc;
  FiniteMapArgsVisitor fmav(evars, predDeclMap, e->efac());
  return visit(fmav, e, dvc);
}

namespace fmap_transf {

inline Expr mkFMIte(Expr c, Expr t, Expr e) {

  if (!seahorn::FmapsNegCond)
    return boolop::lite(c, t, e);
  else
    return boolop::lite(boolop::lneg(c), e, t);
}

Expr mkGetCore(Expr map, Expr key) {

  Expr fmv =
      isOpX<ITE>(map) ? mkIteCore(map->left(), map->right(), map->last()) : map;

  if (fmap::isFmapVal(fmv))
    return mkGetValCore(fmv, key);
  else
    return fmap::mkGet(fmv, key);
}

Expr mkSetCore(Expr map, Expr key, Expr v) {

  Expr fmv =
      isOpX<ITE>(map) ? mkIteCore(map->left(), map->right(), map->last()) : map;

  if (fmap::isFmapVal(fmv))
    return mkSetValCore(fmv, key, v);
  else
    return fmap::mkSet(fmv, key, v);
}

Expr mkIteCore(Expr cond, Expr fm1, Expr fm2) {

  Expr fmv1 = isOpX<ITE>(fm1)
                  ? mkIteCore(fm1->first(), fm1->right(), fm1->last())
                  : fm1;
  Expr fmv2 = isOpX<ITE>(fm2)
                  ? mkIteCore(fm2->first(), fm2->right(), fm2->last())
                  : fm2;
  return mkIteValCore(cond, fmv1, fmv2);
}

Expr mkSameKeysCore(Expr e) {
  Expr ksl = fmap::fmapValKeys(e->left());
  Expr ksr = e->right();

  assert(isOpX<CONST_FINITE_MAP_KEYS>(ksl));
  assert(isOpX<CONST_FINITE_MAP_KEYS>(ksr));
  assert(ksl->arity() == ksr->arity());

  ExprVector conj(ksl->arity());
  auto c_it = conj.begin();
  auto r_it = ksr->begin();
  for (auto l_it = ksl->begin(); l_it != ksl->end(); c_it++, l_it++, r_it++)
    *c_it = mk<EQ>(*l_it, *r_it);

  return boolop::land(conj);
}

Expr inlineVals(Expr e, ExprMap &valmap) {
  FMVisitor dv(valmap);
  DagVisitCache cache;
  Expr newE = visit(dv, e, cache);
  return newE;
}

void insertVarsVal(Expr fmv, ExprSet &vars) {
  Expr ks = fmap::fmapValKeys(fmv);
  for (auto k_it = ks->begin(); k_it != ks->end(); k_it++)
    vars.insert(*k_it);

  Expr vs = fmap::fmapValValues(fmv);
  for (auto v_it = vs->begin(); v_it != vs->end(); v_it++)
    vars.insert(*v_it);
}

Expr expandToVal(Expr fm) {
  Expr fmv;

  if (fmap::isFmapVal(fm))
    fmv = fm;
  else if (isOpX<ITE>(fm))
    fmv = fmap_transf::mkIteCore(fm->left(), fm->right(), fm->last());
  else if (isOpX<SET>(fm))
    fmv = fmap_transf::mkSetCore(fm->left(), fm->right(), fm->last());

  assert(fmap::isFmapVal(fmv));
  return fmv;
}

} // namespace fmap_transf

} // namespace seahorn
