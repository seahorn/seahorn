/// All Expr utilitiies.
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprMemUtils.h"
#include "seahorn/Expr/ExprNumericUtils.hh"
#include "seahorn/Expr/ExprSimplifier.hh"
#include "seahorn/Expr/ExprVisitor.hh"
#include "seahorn/Support/Stats.hh"

#include "seahorn/boost_flat_set.hh"
/// yet to be refactored
namespace expr {

namespace {
struct CIRCSIZE : public std::unary_function<Expr, VisitAction> {
  unsigned ands;
  unsigned ors;
  unsigned inputs;

  CIRCSIZE() : ands(0), ors(0), inputs(0) {}

  VisitAction operator()(Expr e) {
    if (isOpX<AND>(e))
      ands++;
    else if (isOpX<OR>(e))
      ors++;
    else if (!isOpX<NEG>(e)) {
      inputs++;
      return VisitAction::skipKids();
    }
    return VisitAction::doKids();
  }

  unsigned size() { return ands + ors + inputs; }
};
} // namespace

namespace op {
namespace boolop {

/// size of an expression in terms of ANDs, ORs, and inputs.
/// NEG is not counted, other BoolOps are treated as inputs.
unsigned circSize(Expr e) {
  CIRCSIZE csz;
  dagVisit(csz, e);
  return csz.size();
}

unsigned circSize(const ExprVector &vec) {
  CIRCSIZE csz;
  dagVisit(csz, vec);
  return csz.size();
}
} // namespace boolop

namespace array {

Expr storeMapNew(Expr arr, Expr base, Expr ovA, Expr ovB, StoreMapCache &c) {
  // seahorn::ScopedStats _st("smap_new_time");
  Expr map = mk<CONS>(ovA, mk<CONS>(ovB));
  Expr res = mk<STORE_MAP>(arr, base, map);
  Expr oA = ovA->arg(0), vA = ovA->arg(1);
  Expr oB = ovB->arg(0), vB = ovB->arg(1);
  unsigned long oANum = op::bv::toMpz(oA).get_ui(),
                oBNum = op::bv::toMpz(oB).get_ui();
  OffsetValueMap *ovMap = new OffsetValueMap();
  ovMap->insert({oANum, vA});
  ovMap->insert({oBNum, vB});
  c[&*res] = ovMap;
  res->Ref();
  return res;
}

bool ovCmp(const Expr a, const Expr b) {
  // both a and b are struct(offset, val)
  ENode *oA = a->arg(0);
  ENode *oB = b->arg(0);
  assert(op::bv::is_bvnum(oA));
  assert(op::bv::is_bvnum(oB));
  return op::bv::toMpz(oA).get_ui() < op::bv::toMpz(oB).get_ui();
}

void transferStoreMapCache(ENode *oldE, ENode *newE, StoreMapCache &c) {
  c[newE] = c[oldE];
  newE->Ref();
  // remove
  c[oldE] = nullptr;
  c.erase(oldE);
  oldE->efac().Deref(oldE);
}

Expr storeMapInsert(Expr stm, Expr ov, StoreMapCache &c) {
  // seahorn::ScopedStats _st("smap_insert_time");
  Expr smap = storeMapGetMap(stm);
  smap = mk<CONS>(ov, smap);
  Expr res =
      stm->efac().mkTern(stm->op(), stm->arg(0), stm->arg(1), smap);
  // update in cached map
  auto mapIt = c.find(&*stm);
  if (mapIt != c.end()) {
    op::array::OffsetValueMap *map = mapIt->second;
    Expr o = ov->arg(0), v = ov->arg(1);
    (*map)[op::bv::toMpz(o).get_ui()] = v;
    transferStoreMapCache(&*stm, &*res, c);
  } // else is probably going wrong
  return res;
}

Expr storeMapFind(Expr stm, Expr o, StoreMapCache &c) {
  // XXX AG: This has potential to leak memory. Needs closer review/rewrite
  // seahorn::ScopedStats _st("smap_find_time");
  Expr res;
  unsigned long oNum = op::bv::toMpz(o).get_ui();
  auto it = c.find(&*stm);
  if (it != c.end() && op::bv::is_bvnum(o)) {
    auto v = it->second->find(oNum);
    if (v != it->second->end()) {
      seahorn::Stats::count("hybrid.smap_find_w_cache");
      res = v->second;
    }
    return res;
  }
  // Fallback:
  Expr head = op::array::storeMapGetMap(stm);
  Expr ov;
  OffsetValueMap *ovM = new OffsetValueMap();
  while (head) {
    ov = head->arg(0);
    head = head->arity() == 2 ? head->arg(1) : nullptr;
    Expr oX = ov->arg(0);
    unsigned long oXNum = op::bv::toMpz(oX).get_ui();
    if (!res && oXNum == oNum) { /* Find first */
      seahorn::Stats::count("hybrid.smap_find_w_fallback");
      res = ov->arg(1);
    }
    if (ovM->find(oXNum) ==
        ovM->cend()) { // reconstruct cache using values towards head
      ovM->insert({oXNum, ov->arg(1)});
    }
  }
  assert(c.count(&*stm) == 0);
  // XXX AG: This is only ok if this key is inserted into this map for the first time
  c[&*stm] = ovM;
  stm->Ref();
  return res;
}

// ENode * => std::map<unsigned, Expr> *
void clearStoreMapCache(StoreMapCache &cache) {
  seahorn::ScopedStats _st("clear-store-map-cache");
  for (StoreMapCache::value_type &kv : cache) {
    kv.first->efac().Deref(kv.first);
    kv.second->clear();
    delete kv.second;
  }
  cache.clear();
}

} // namespace array

} // namespace op

namespace {
struct SIZE : public std::unary_function<Expr, VisitAction> {
  size_t count;

  SIZE() : count(0) {}

  VisitAction operator()(Expr exp) {
    count++;
    return VisitAction::doKids();
  }
};
} // namespace

/** Size of an expression as a DAG */
size_t dagSize(Expr e) {
  SIZE sz;
  dagVisit(sz, e);
  return sz.count;
}

size_t dagSize(const ExprVector &vec) {
  SIZE sz;
  dagVisit(sz, vec);
  return sz.count;
}

/** Size of an expression as a tree */
size_t treeSize(Expr e) {
  SIZE sz;
  treeVisit(sz, e);
  return sz.count;
}

namespace {
struct CV : public std::unary_function<Expr, VisitAction> {
  Expr e;
  bool found;
  ExprSet seen;

  CV(const CV &o) : e(o.e), found(o.found), seen(o.seen) {
    llvm_unreachable(nullptr);
  }

  CV(Expr exp) : e(exp), found(false) {}

  VisitAction operator()(Expr exp) {
    if (found || seen.count(exp) > 0 || e == exp) {
      found = true;
      return VisitAction::skipKids();
    }
    seen.insert(e);
    return VisitAction::doKids();
  }
};
} // namespace

/** Returns true if e1 contains e2 as a sub-expression */
bool contains(Expr e1, Expr e2) {
  CV cv(e2);
  dagVisit(cv, e1);
  return cv.found;
}

namespace {
struct RAV : public std::unary_function<Expr, VisitAction> {
  Expr s;
  Expr t;

  RAV(const RAV &o) : s(o.s), t(o.t) {}
  RAV(Expr _s, Expr _t) : s(_s), t(_t) {}
  VisitAction operator()(Expr exp) const {
    return exp == s ? VisitAction::changeTo(t) : VisitAction::doKids();
  }
};
} // namespace
// -- replace all occurrences of s by t
Expr replaceAll(Expr exp, Expr s, Expr t) {
  RAV rav(s, t);
  return dagVisit(rav, exp);
}

namespace {
struct RAVSIMP : public std::unary_function<Expr, VisitAction> {
  Expr s;
  Expr t;

  std::shared_ptr<boolop::TrivialSimplifier> r;

  RAVSIMP(const RAVSIMP &o) : s(o.s), t(o.t), r(o.r) {}
  RAVSIMP(Expr _s, Expr _t)
      : s(_s), t(_t),
        r(std::make_shared<boolop::TrivialSimplifier>(s->efac())) {}

  VisitAction operator()(Expr exp) const {
    if (exp == s)
      return VisitAction::changeTo(t);
    return VisitAction::changeDoKidsRewrite(exp, r);
  }
};
} // namespace

/** Replace all occurrences of s by t while simplifying the result */
Expr replaceAllSimplify(Expr exp, Expr s, Expr t) {
  RAVSIMP rav(s, t);
  return dagVisit(rav, exp);
}

namespace op {
namespace boolop {
/**
 * Very simple simplifier for Boolean Operators
 */
Expr simplify(Expr exp) {
  BS<TrivialSimplifier> bs(std::make_shared<TrivialSimplifier>(exp->efac()));
  return dagVisit(bs, exp);
}

bool areNegations(Expr lhs, Expr rhs) {
  /** a negates !a**/
  if (isOpX<NEG>(lhs) && lhs->left() == rhs)
    return true;
  if (isOpX<NEG>(rhs) && rhs->left() == lhs)
    return true;

  return false;
}

namespace {
/** Rewriter that normalizes AND/OR operators */
struct NormalizeOps : public std::unary_function<Expr, Expr> {
  Expr trueE;
  Expr falseE;

  NormalizeOps() : trueE(0), falseE(0) {}

  NormalizeOps(const NormalizeOps &o) : trueE(o.trueE), falseE(o.falseE) {}

  Expr operator()(Expr exp) {
    // -- create true/false constants for convinience
    if (trueE == nullptr) {
      trueE = mk<TRUE>(exp->efac());
      falseE = mk<FALSE>(exp->efac());
    }

    // -- skip anything that is not AND/OR
    if (!(isOpX<AND>(exp) || isOpX<OR>(exp)))
      return exp;
    if (exp->arity() == 1)
      return exp->left();

    const Operator &op = exp->op();
    Expr top, bot;
    if (isOpX<AND>(exp)) {
      top = trueE;
      bot = falseE;
    } else {
      top = falseE;
      bot = trueE;
    }

    if (exp->arity() == 0)
      return top;

    if (exp->arity() == 2) {
      if (isOpX<AND>(exp))
        return land(exp->left(), exp->right());
      else /* isOpX<OR> */
        return lor(exp->left(), exp->right());
    }

    ExprSet newArgs;
    for (Expr a : mk_it_range(exp->args_begin(), exp->args_end()))
      if (!(op == a->op())) {
        if (a == bot)
          return bot;
        else if (a != top)
          newArgs.insert(a);
      } else /* descend into kids that have the same top-level operator */
        for (Expr ka : mk_it_range(a->args_begin(), a->args_end()))
          if (ka == bot)
            return bot;
          else if (ka != top)
            newArgs.insert(ka);

    if (newArgs.empty())
      return top;
    if (newArgs.size() == 1)
      return *(newArgs.begin());

    boost::container::flat_set<Expr> args(newArgs.begin(), newArgs.end());
    Expr res = top;
    for (Expr arg : llvm::reverse(args))
      res = isOpX<AND>(exp) ? land(arg, res) : lor(arg, res);

    return res;
  }

  Expr land(Expr f, Expr g) {
    /** base cases */
    if (f == trueE)
      return g;
    if (g == trueE)
      return f;
    if (f == falseE || g == falseE)
      return falseE;
    if (f == g)
      return f;
    if (f == boolop::lneg(g) || boolop::lneg(f) == g)
      return falseE;

    // -- both not AND operators. Order in some way
    if (!isOpX<AND>(f) && !isOpX<AND>(g))
      return g < f ? mk<AND>(f, g) : mk<AND>(g, f);

    Expr topf = isOpX<AND>(f) ? f->left() : f;
    Expr topg = isOpX<AND>(g) ? g->left() : g;

    Expr top, restF, restG;
    if (topf < topg || topf == topg) {
      top = topf;
      restF = isOpX<AND>(f) ? f->right() : trueE;
    } else
      restF = f;

    if (topg < topf || topg == topf) {
      top = topg;
      restG = isOpX<AND>(g) ? g->right() : trueE;
    } else
      restG = g;

    return boolop::land(top, land(restF, restG));
  }

  Expr lor(Expr f, Expr g) {
    /** base cases */
    if (f == falseE)
      return g;
    if (g == falseE)
      return f;
    if (f == trueE || g == trueE)
      return trueE;
    if (f == g)
      return f;
    if (f == boolop::lneg(g) || boolop::lneg(f) == g)
      return trueE;

    // -- both not AND operators. Order in some way
    if (!isOpX<OR>(f) && !isOpX<OR>(g))
      return g < f ? mk<OR>(f, g) : mk<OR>(g, f);

    Expr topf = isOpX<OR>(f) ? f->left() : f;
    Expr topg = isOpX<OR>(g) ? g->left() : g;

    Expr top, restF, restG;
    if (topf < topg || topf == topg) {
      top = topf;
      restF = isOpX<OR>(f) ? f->right() : falseE;
    } else
      restF = f;

    if (topg < topf || topg == topf) {
      top = topg;
      restG = isOpX<OR>(g) ? g->right() : falseE;
    } else
      restG = g;

    return boolop::lor(top, lor(restF, restG));
  }
};
} // namespace
/**
 * Very simple normalizer for AND/OR expressions
 */
Expr norm(Expr exp) {
  BS<NormalizeOps> bs(new NormalizeOps());
  return dagVisit(bs, exp);
}

namespace {
/** Rewriter that gathers Boolean operators into n-ary ones */
struct GatherOps : public std::unary_function<Expr, Expr> {
  Expr trueE;
  Expr falseE;

  GatherOps() : trueE(0), falseE(0) {}

  GatherOps(const GatherOps &o) : trueE(o.trueE), falseE(o.falseE) {}

  Expr operator()(Expr exp) {
    // -- create true/false constants for convinience
    if (trueE == nullptr) {
      trueE = mk<TRUE>(exp->efac());
      falseE = mk<FALSE>(exp->efac());
    }

    // -- skip terminals
    if (exp->arity() == 0)
      return exp;
    // if (!isBoolOp<X> (exp)) return exp;
    // -- skip anything that is not AND/OR
    if (!(isOpX<AND>(exp) || isOpX<OR>(exp)))
      return exp;

    const Operator &op = exp->op();
    Expr top;
    Expr bot;
    if (isOpX<AND>(exp)) {
      top = trueE;
      bot = falseE;
    } else {
      top = falseE;
      bot = trueE;
    }

    ExprSet newArgs;
    for (Expr a : mk_it_range(exp->args_begin(), exp->args_end()))
      if (!(op == a->op())) {
        if (a == bot)
          return bot;
        else if (a != top)
          newArgs.insert(a);
      } else /* descend into kids that have the same top-level operator */
        for (Expr ka : mk_it_range(a->args_begin(), a->args_end()))
          if (ka == bot)
            return bot;
          else if (ka != top)
            newArgs.insert(ka);

    if (newArgs.empty())
      return top;
    if (newArgs.size() == 1)
      return *(newArgs.begin());
    return exp->efac().mkNary(op, newArgs.begin(), newArgs.end());
  }
};
} // namespace

/** Gather binary Boolean operators into n-ary ones. Helps
    readability. Best done after NNF */
Expr gather(Expr exp) {
  BS<GatherOps> go(new GatherOps());
  return dagVisit(go, exp);
}

namespace {
/** puts an expression into NNF */
struct NNF : public std::unary_function<Expr, VisitAction> {
  ExprFactory &efac;
  std::shared_ptr<TrivialSimplifier> r;

  NNF(const NNF &o) : efac(o.efac), r(o.r) {}

  NNF(ExprFactory &fac)
      : efac(fac), r(std::make_shared<TrivialSimplifier>(efac)) {}

  VisitAction operator()(Expr exp) {
    if (exp->arity() == 0)
      return VisitAction::skipKids();

    // -- AND / OR -- run the simplifier
    if (isOpX<AND>(exp) || isOpX<OR>(exp))
      return VisitAction::changeDoKidsRewrite(exp, r);

    // -- not a negation, then do not touch, must be non-Boolean
    if (!isOpX<NEG>(exp))
      return VisitAction::skipKids();

    // -- if here, top operator is negation, push it in
    Expr lhs = exp->left();
    if (lhs == r->falseE)
      return VisitAction::changeTo(r->trueE);
    if (lhs == r->trueE)
      return VisitAction::changeTo(r->falseE);

    // -- !!x -- Trivial simplifer will get rid of unary AND
    if (isOpX<NEG>(lhs))
      return VisitAction::changeDoKidsRewrite(mk<AND>(lhs->left()), r);

    // -- ! (x & b) ==> !x || !b
    if (isOpX<OR>(lhs) || isOpX<AND>(lhs)) {
      // -- negate arguments
      ExprVector args;
      for (Expr arg : mk_it_range(lhs->args_begin(), lhs->args_end()))
        args.push_back(lneg(arg));

      // -- flip operator
      Expr res = isOpX<OR>(lhs) ? mknary<AND>(args.begin(), args.end())
                                : mknary<OR>(args.begin(), args.end());
      return VisitAction::changeDoKidsRewrite(res, r);
    }

    // -- negation of anything else, don't descend
    return VisitAction::skipKids();
  }
};

} // namespace
/**
 * Converts to NNF. Assumes the only Boolean operators of exp
 * are AND/OR/NEG.
 */
Expr nnf(Expr exp) {
  NNF n(exp->efac());
  return dagVisit(n, exp);
}

/** Makes an expression pretty for printing */
Expr pp(Expr exp) { return gather(nnf(exp)); }
} // namespace boolop
} // namespace op
namespace numeric {

bool getNum(Expr exp, mpz_class &num) {
  if (isOp<MPZ>(exp)) {
    num = getTerm<mpz_class>(exp);

    return true;
  } else if (isOp<UINT>(exp)) {
    unsigned unsignedNum = getTerm<unsigned>(exp);
    num = mpz_class(unsignedNum);

    return true;
  } else if (bv::is_bvnum(exp)) {
    num = bv::toMpz(exp);

    return true;
  }

  return false;
}

bool isNumeric(Expr exp) {
  return isOp<MPZ>(exp) || isOp<UINT>(exp) || bv::is_bvnum(exp);
}

Expr convertToMpz(Expr exp) {
  mpz_class num = 0;
  if (getNum(exp, num)) {
    return mkTerm<mpz_class>(num, exp->efac());
  }

  return exp;
}
} // namespace numeric
namespace mem {
using namespace addrRangeMap;
inline bool isBasedObjAddr(Expr e) {
  if (op::bv::isBvConst(e)) {
    // strip fdecl
    Expr name = op::bind::fname(e);
    if (op::bind::isFdecl(name)) {
      name = op::bind::fname(name);
    }
    // strip variant
    if (isOpX<VARIANT>(name)) {
      name = op::variant::mainVariant(name);
    }
    if (isOpX<STRING>(name)) {
      std::string term = getTerm<std::string>(name);
      if (term.rfind("sea.obj", 0) == 0)
        return true;
    }
  }
  return false;
}

int getBasedAddrSerial(Expr e) {
  assert(isBasedObjAddr(e));
  Expr name = op::bind::fname(e);
  if (op::bind::isFdecl(name)) {
    name = op::bind::fname(name);
  }
  // strip variant
  if (isOpX<VARIANT>(name)) {
    return op::variant::variantNum(name);
  }
  return -1;
}

bool isBaseAddr(Expr e) { return isBasedObjAddr(e); }

bool isSingleBasePtr(Expr e, size_t ptrWidth, Expr &base, Expr &offset) {
  if (isBaseAddr(e)) {
    base = e;
    offset = op::bv::bvnum(0UL, ptrWidth, e->efac());
    return true;
  }
  if (isOpX<BADD>(e)) {
    Expr b;
    ExprVector offsets;
    for (auto it = e->args_begin(); it != e->end(); it++) {
      if (isBaseAddr(*it)) {
        b = *it;
      } else {
        offsets.push_back(*it);
      }
    }
    if (!b)
      return false;
    base = b;
    if (offsets.size() == 1) {
      offset = offsets[0];
    } else if (offsets.empty()) {
      offset = op::bv::bvnum(0UL, ptrWidth, e->efac());
    } else {
      offset = mknary<BADD>(offsets.begin(), offsets.end());
    }
    return true;
  }
  return false;
}

void updatePtrTCCache(const Expr &e, bool isPtr, PtrTypeCheckCache &cache) {
  if (e->use_count() > 1) {
    e->Ref();
    cache[&*e] = isPtr;
  }
}

bool isPtrExpr(Expr e, PtrTypeCheckCache &cache) {
  if (isBaseAddr(e)) {
    return true;
  }
  if (isOpX<BSUB>(e)) {
    return false; // even if two ptrs subtract, will yield offset
  }
  if (op::bv::isBvConst(e) || op::bv::is_bvnum(e)) {
    return false;
  }

  if (e->use_count() > 1) {
    auto cit = cache.find(&*e);
    if (cit != cache.end()) {
      return cit->second;
    }
  }

  // AG XXX: Except for ITE this looks wrong
  // AG XXX: ptr-expressions should not be glued out of other parts
  bool res = false;
  if (isOpX<ITE>(e)) {
    Expr a = e->arg(1);
    Expr b = e->arg(2);
    res = isPtrExpr(a, cache) || isPtrExpr(b, cache);
  } else if (isOpX<BCONCAT>(e)) {
    res = isPtrExpr(e->arg(0), cache) || isPtrExpr(e->arg(1), cache);
  } else if (isOpX<BEXTRACT>(e)) {
    res = isPtrExpr(op::bv::earg(e), cache);
  } else {
    // AG XXX: this probably handles pointer arithmetic, i.e., BADD
    for (auto it = e->args_begin(); it != e->args_end(); it++) {
      if (isPtrExpr(*it, cache)) {
        res = true;
        break;
      }
    }
  }
  updatePtrTCCache(e, res, cache);
  return res;
}

bool isZeroBits(Expr e, PtrBitsZeroed &p) {
  if (isOpX<BCONCAT>(e)) {
    Expr lhs = e->arg(0);
    Expr rhs = e->arg(1);
    if (isOpX<BEXTRACT>(lhs) && op::bv::is_bvnum(rhs)) {
      mpz_class rhsMpz = op::bv::toMpz(rhs);
      if (rhsMpz.get_ui() == 0) {
        unsigned lowBits = op::bv::low(lhs);
        p.first = op::bv::earg(lhs);
        p.second = lowBits;
        return true;
      }
    }
  }
  return false;
}
} // namespace mem

} // namespace expr
