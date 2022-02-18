#include "seahorn/Expr/ExprAddrRangeMap.hh"
#include "seahorn/Expr/ExprMemUtils.h"

namespace expr {
namespace addrRangeMap {

void AddrRangeMap::addRange(const AddrRange &range) {
  for (auto b = begin(); b != end(); b++) {
    m_rangeMap[b->first] = b->second + range;
  }
}

void AddrRangeMap::zeroBits(size_t n) {
  for (auto b = begin(); b != end(); b++) {
    m_rangeMap[b->first] = zeroBitsRange(b->second, n);
  }
}

AddrRangeMap AddrRangeMap::unionWith(AddrRangeMap &b) {
  AddrRangeMap res(m_rangeMap, m_isAllTop || b.isAllTop());
  for (auto bEntry = b.cbegin(); bEntry != b.cend(); bEntry++) {
    auto aEntry = m_rangeMap.find(bEntry->first);
    if (aEntry != m_rangeMap.end()) {
      AddrRange bRange = bEntry->second;
      AddrRange aRange = aEntry->second;
      res[bEntry->first] = aRange | bRange;
    } else { // insert entry into a
      res[bEntry->first] = bEntry->second;
    }
  }
  return res;
}

bool AddrRangeMap::contains(Expr base, unsigned offset) {
  if (m_isAllTop)
    return true;

  auto entry = m_rangeMap.find(base);
  if (entry == m_rangeMap.end())
    return false; /* base key not in map */
  return entry->second.contains(offset);
}

template <typename T> void AddrRangeMap::print(T &OS) const {
  if (m_isAllTop) {
    OS << "{ all => top } \n";
  } else {
    OS << "{\n";
    for (auto m = m_rangeMap.begin(); m != m_rangeMap.end(); m++) {
      auto range = m->second;
      OS << "  " << *m->first << " => ";
      if (range.isTop)
        OS << "any\n";
      else
        OS << "(" << range.low << ", " << range.high << ")\n";
    }
    OS << "}\n";
  }
}

bool AddrRangeMap::isValid() {
  if (m_isAllTop)
    return true;
  for (auto b : m_rangeMap) {
    if (!expr::mem::isBaseAddr(b.first))
      return false;
    if (!b.second.isValid())
      return false;
  }
  return true;
}

llvm::raw_ostream &operator<<(llvm::raw_ostream &OS, AddrRangeMap const &arm) {
  arm.print(OS);
  return OS;
}

std::ostream &operator<<(std::ostream &OS, AddrRangeMap const &arm) {
  arm.print(OS);
  return OS;
}

AddrRange zeroBitsRange(AddrRange &r, size_t bits) {
  unsigned new_low = r.low >> bits;
  new_low = new_low << bits;
  unsigned new_high = r.high >> bits;
  new_high = new_high << bits;
  return AddrRange(new_low, new_high, r.isTop);
}

AddrRange addrRangeOf(Expr e) {
  if (op::bv::is_bvnum(e)) {
    mpz_class offsetMpz = op::bv::toMpz(e);
    auto offsetNum = offsetMpz.get_ui();
    return AddrRange(offsetNum, offsetNum, false);
  }
  if (isOpX<BADD>(e)) {
    AddrRange res;
    for (auto b = e->args_begin(); b != e->args_end(); ++b) {
      AddrRange range = addrRangeOf(*b);
      res = res + range;
    }
    return res;
  }
  if (isOpX<ITE>(e)) {
    AddrRange tRange = addrRangeOf(e->arg(1));
    AddrRange eRange = addrRangeOf(e->arg(2));
    return tRange | eRange;
  }
  /* assume is symbolic */
  return AddrRange(0, 0, true);
}

inline void updateARMCache(ARMCache &cache, Expr e, AddrRangeMap arm) {
  if (e->use_count() > 1) {
    // expr->Ref();
    cache[&*e] = arm;
  }
}

AddrRangeMap addrRangeMapOf(Expr e, ARMCache &cache) {
  if (e->use_count() > 1) {
    ARMCache::const_iterator cit = cache.find(&*e);
    if (cit != cache.end())
      return cit->second;
  }
  if (mem::isBaseAddr(e)) {
    AddrRangeMap res = AddrRangeMap({{e, AddrRange(0, 0)}});
    updateARMCache(cache, e, res);
    return res;
  }
  if (isOpX<BADD>(e)) {
    Expr base;
    llvm::SmallVector<Expr, 2> offsets;
    for (auto b = e->args_begin(); b != e->args_end(); ++b) {
      /* try to find a base and offsets */
      if (mem::isPtrExpr(*b)) {
        base = *b;
      } else {
        offsets.push_back(*b);
      }
    }
    if (base == NULL) {
      AddrRangeMap res = AddrRangeMap({{}}, true); // Fallback to { all => any }
      updateARMCache(cache, e, res);
      return res;
    }
    AddrRangeMap res = addrRangeMapOf(base, cache);
    for (auto o : offsets) {
      AddrRange oRange = addrRangeOf(o);
      res.addRange(oRange);
    }
    updateARMCache(cache, e, res);
    return res;
  }
  if (isOpX<ITE>(e)) {
    AddrRangeMap a = addrRangeMapOf(e->arg(1), cache);
    AddrRangeMap b = addrRangeMapOf(e->arg(2), cache);
    /* merge t e into t*/
    AddrRangeMap res = a.unionWith(b);
    updateARMCache(cache, e, res);
    return res;
  }
  // Align pointer
  // any known operation that zeroes out last k bits
  mem::PtrBitsZeroed ptrBits;
  if (mem::isZeroBits(e, ptrBits)) {
    AddrRangeMap res = addrRangeMapOf(ptrBits.first, cache);
    res.zeroBits(ptrBits.second);
    updateARMCache(cache, e, res);
    return res;
  }

  // fallback: {all => any}
  AddrRangeMap res = AddrRangeMap({{}}, true);
  updateARMCache(cache, e, res);
  return res;
}

}; // namespace addrRangeMap
}; // namespace expr