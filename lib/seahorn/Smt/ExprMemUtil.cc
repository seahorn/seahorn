#include "seahorn/Expr/ExprMemUtil.hh"
#include "seahorn/Expr/Expr.hh"

#include "seahorn/Support/Stats.hh"

namespace expr {
namespace op {
namespace array {

Expr storeMapNew(Expr arr, Expr base, Expr ovA, Expr ovB, StoreMapCache &c) {
  // seahorn::ScopedStats _st("smap_new_time");
  Expr map = mk<CONS>(ovA, mk<CONS>(ovB));
  Expr res = mk<STORE_MAP>(arr, base, map);

  Expr oA = ovA->arg(0), vA = ovA->arg(1);
  Expr oB = ovB->arg(0), vB = ovB->arg(1);
  unsigned long oANum = op::bv::toMpz(oA).get_ui(),
                oBNum = op::bv::toMpz(oB).get_ui();
  auto ovMap = std::make_unique<OffsetValueMap>();
  ovMap->insert({oANum, vA});
  ovMap->insert({oBNum, vB});
  c.insert({&*res, std::move(ovMap)});

  res->Ref();

  return res;
}

bool ovLessThen(const Expr &a, const Expr &b) {
  // both a and b are struct(offset, val)
  ENode *oA = a->arg(0);
  ENode *oB = b->arg(0);
  assert(op::bv::is_bvnum(oA));
  assert(op::bv::is_bvnum(oB));
  return op::bv::toMpz(oA).get_ui() < op::bv::toMpz(oB).get_ui();
}

void transferStoreMapCache(ENode *fromE, ENode *toE, StoreMapCache &cache) {
  toE->Ref();
  std::swap(cache[toE], cache[fromE]);

  // remove old value
  cache.erase(fromE);
  fromE->efac().Deref(fromE);
}

Expr storeMapInsert(Expr stm, Expr ov, StoreMapCache &c) {
  // seahorn::ScopedStats _st("smap_insert_time");
  Expr smap = mk<CONS>(ov, storeMapGetMap(stm));
  Expr res = stm->efac().mkTern(stm->op(), stm->arg(0), stm->arg(1), smap);

  // update in cached map
  auto mapIt = c.find(&*stm);
  if (mapIt != c.end()) {
    auto &map = mapIt->second;
    Expr o = ov->arg(0), v = ov->arg(1);
    map->insert({op::bv::toMpz(o).get_ui(), v});
    transferStoreMapCache(&*stm, &*res, c);
  } // else is probably going wrong
  else {
    // AG : XXX : Maybe cache store map?
    assert(false);
  }

  return res;
}

Expr storeMapFind(Expr stm, Expr o, StoreMapCache &c) {
  // seahorn::ScopedStats _st("smap_find_time");
  Expr res;

  assert(op::bv::is_bvnum(o));
  unsigned long oNum = op::bv::toMpz(o).get_ui();

  auto it = c.find(&*stm);
  if (it != c.end()) {
    auto v = it->second->find(oNum);
    if (v != it->second->end()) {
      seahorn::Stats::count("hybrid.smap_find_w_cache");
      res = v->second;
    }
    assert(res);
    return res;
  }

  // Fallback:
  Expr head = op::array::storeMapGetMap(stm);
  Expr ov;
  std::unique_ptr<OffsetValueMap> ovM = std::make_unique<OffsetValueMap>();
  while (head) {
    ov = head->arg(0);
    head = head->arity() == 2 ? head->arg(1) : Expr();
    Expr oX = ov->arg(0);
    unsigned long oXNum = op::bv::toMpz(oX).get_ui();
    if (!res && oXNum == oNum) { /* Find first */
      seahorn::Stats::count("hybrid.smap_find_w_fallback");
      res = ov->arg(1);
    }
    if (ovM->find(oXNum) == ovM->cend()) {
      // reconstruct cache using values towards head
      ovM->insert({oXNum, ov->arg(1)});
    }
  }
  assert(c.count(&*stm) == 0);
  c.insert({&*stm, std::move(ovM)});
  stm->Ref();
  return res;
}

// ENode * => std::map<unsigned, Expr> *
void clearStoreMapCache(StoreMapCache &cache) {
  seahorn::ScopedStats _st("clear-store-map-cache");
  for (StoreMapCache::value_type &kv : cache) {
    kv.first->efac().Deref(kv.first);
    kv.second->clear();
  }
  cache.clear();
}

} // namespace array
} // namespace op

namespace mem {

bool isBasedObjAddr(Expr e) {
  if (!op::bv::isBvConst(e))
    return false;

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
    auto term = getTerm<std::string>(name);
    return term.rfind("sea.obj", 0) == 0;
  }

  return false;
}

bool isBaseAddr(Expr e) { return isBasedObjAddr(e); }

int getBasedAddrSerial(Expr e) {
  assert(isBasedObjAddr(e));
  Expr name = op::bind::fname(e);
  if (op::bind::isFdecl(name)) {
    name = op::bind::fname(name);
  }

  if (isOpX<VARIANT>(name)) {
    return op::variant::variantNum(name);
  }
  return -1;
}

bool isSingleBasePtr(Expr e, size_t ptrWidth, Expr &base, Expr &offset) {
  if (isBaseAddr(e)) {
    base = e;
    offset = op::bv::bvnum(0UL, ptrWidth, e->efac());
    return true;
  }

  if (isOpX<BADD>(e)) {
    Expr b;
    llvm::SmallVector<Expr, 4> offsets;
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
