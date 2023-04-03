#include "seahorn/Expr/ExprAddrRangeMap.hh"
#include "seahorn/Expr/ExprMemUtils.h"
#include "seahorn/Support/Stats.hh"

namespace expr {
namespace addrRangeMap {

bool AddrRange::isValid() {
  if (m_isTop && m_isBot)
    return false;
  if (m_isTop)
    return m_low == std::numeric_limits<unsigned>::min() &&
           m_high == std::numeric_limits<unsigned>::max();
  if (m_isBot)
    return m_high == std::numeric_limits<unsigned>::min() &&
           m_low == std::numeric_limits<unsigned>::max();

  return m_low <= m_high;
}

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

AddrRangeMap addrRangeMapUnion(AddrRangeMap &a, AddrRangeMap &b) {
  if (a.isAllBot())
    return b;
  if (b.isAllBot())
    return a;
  if (a.isAllTop() || b.isAllTop())
    return mkARMTop();
  AddrRangeMap res(a);
  for (auto bEntry = b.cbegin(); bEntry != b.cend(); bEntry++) {
    auto aEntry = a.find(bEntry->first);
    if (aEntry != a.end()) {
      AddrRange bRange = bEntry->second;
      AddrRange aRange = aEntry->second;
      res[bEntry->first] = aRange | bRange;
    } else { // insert entry into a
      res[bEntry->first] = bEntry->second;
    }
  }
  return res;
}

AddrRangeMap addrRangeMapIntersect(AddrRangeMap &a, AddrRangeMap &b) {
  /* appropriate to time here since intersect is only used for compare*/
  seahorn::ScopedStats _st_("hybrid.arm_compare");
  if (a.isAllTop())
    return b;
  if (b.isAllTop())
    return a;
  if (a.isAllBot() || b.isAllBot())
    return mkARMBot();
  AddrRangeMap res;
  bool isBot = true;
  for (auto bEntry = b.cbegin(); bEntry != b.cend(); bEntry++) {
    auto aEntry = a.find(bEntry->first);
    if (aEntry != a.end()) {
      AddrRange bRange = bEntry->second;
      AddrRange aRange = aEntry->second;
      AddrRange nRange = aRange & bRange;
      if (!nRange.m_isBot) {
        res[bEntry->first] = nRange;
        isBot = false;
      }
    }
  }
  if (isBot) {
    res.setBot(true);
    res.setTop(false); // sanity check
  }
  return res;
}

bool AddrRangeMap::contains(Expr base, unsigned offset) {
  if (this->m_isTop)
    return true;

  if (this->m_isBot)
    return false;

  auto entry = m_rangeMap.find(base);
  if (entry == m_rangeMap.end())
    return false; /* base key not in map */
  return entry->second.contains(offset);
}

template <typename T> void AddrRangeMap::print(T &OS) const {
  if (m_isTop) {
    OS << "{ all => top } \n";
  } else if (m_isBot) {
    OS << "{ all => bot } \n";
  } else {
    OS << "size: " << m_rangeMap.size() << "\n";
    OS << "{\n";
    for (auto m = m_rangeMap.begin(); m != m_rangeMap.end(); m++) {
      auto range = m->second;
      OS << "  " << *m->first << " => ";
      if (range.m_isTop)
        OS << "any\n";
      else if (range.m_isBot)
        OS << "none\n";
      else
        OS << "(" << range.m_low << ", " << range.m_high << ")\n";
    }
    OS << "}\n";
  }
}

bool AddrRangeMap::isValid() {
  if (m_isBot && m_isTop)
    return false;
  if (m_isBot || m_isTop)
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
  if (r.m_isBot || r.m_isTop)
    return r;
  unsigned new_low = r.m_low >> bits;
  new_low = new_low << bits;
  unsigned new_high = r.m_high >> bits;
  new_high = new_high << bits;
  return AddrRange(new_low, new_high, r.m_isTop, r.m_isBot);
}

AddrRange addrRangeOf(Expr e) {
  if (op::bv::is_bvnum(e)) {
    mpz_class offsetMpz = op::bv::toMpz(e);
    auto offsetNum = offsetMpz.get_ui();
    return AddrRange(offsetNum, offsetNum);
  }
  if (isOpX<BADD>(e)) {
    AddrRange res;
    for (auto b = e->args_begin(); b != e->args_end(); ++b) {
      AddrRange range = addrRangeOf(*b);
      res = res + range;
    }
    return res;
  }
  if (isOpX<BSUB>(e)) {
    // not covered in intervals domain
    return mkAddrRangeTop();
  }
  if (isOpX<ITE>(e)) {
    AddrRange tRange = addrRangeOf(e->arg(1));
    AddrRange eRange = addrRangeOf(e->arg(2));
    return tRange | eRange;
  }
  /* assume is symbolic */
  return mkAddrRangeTop();
}

inline void updateARMCache(ARMCache &cache, const Expr &e, AddrRangeMap arm) {
  if (e->use_count() > 1) {
    e->Ref();
    cache[&*e] = arm;
  }
}

static AddrRangeMap s_addrRangeMapOf(Expr e, ARMCache &cache,
                                     expr::PtrTypeCheckCache &ptCache) {
  if (e->use_count() > 1) {
    auto cit = cache.find(&*e);
    if (cit != cache.end()) {
      return cit->second;
    }
  }
  if (mem::isBaseAddr(e)) {
    AddrRangeMap res = AddrRangeMap({{e, AddrRange(0, 0)}});
    updateARMCache(cache, e, res);
    return res;
  }
  if (isOpX<BADD>(e)) {
    Expr base;
    llvm::SmallVector<Expr, 4> offsets;
    bool baseFound = false;
    for (auto it = e->args_begin(); it != e->args_end(); ++it) {
      /* try to find a base and offsets */
      if (!baseFound && mem::isPtrExpr(*it, ptCache)) {
        base = *it;
        baseFound = true;
      } else {
        offsets.push_back(*it);
      }
    }
    if (!base) {
      AddrRangeMap res = mkARMTop(); // Fallback to { all => any }
      updateARMCache(cache, e, res);
      return res;
    }
    AddrRangeMap res = s_addrRangeMapOf(base, cache, ptCache);
    AddrRange r = mkAddrRangeBot(); // bot + anything = anything
    for (auto o : offsets) {
      AddrRange oRange = addrRangeOf(o);
      r = r + oRange;
    }
    res.addRange(r);
    updateARMCache(cache, e, res);
    return res;
  }
  if (isOpX<ITE>(e)) {
    AddrRangeMap a = s_addrRangeMapOf(e->arg(1), cache, ptCache);
    AddrRangeMap b = s_addrRangeMapOf(e->arg(2), cache, ptCache);
    /* merge t e into t*/
    if (a.size() < b.size()) {
      std::swap(a, b); // make sure join small (b) into big (a)
    }
    AddrRangeMap res = addrRangeMapUnion(a, b);
    updateARMCache(cache, e, res);
    return res;
  }
  // Align pointer
  // any known operation that zeroes out last k bits
  mem::PtrBitsZeroed ptrBits;
  if (mem::isZeroBits(e, ptrBits)) {
    AddrRangeMap res = s_addrRangeMapOf(ptrBits.first, cache, ptCache);
    res.zeroBits(ptrBits.second);
    updateARMCache(cache, e, res);
    return res;
  }

  // fallback: {all => any}
  AddrRangeMap res = mkARMTop();
  updateARMCache(cache, e, res);
  return res;
}

AddrRangeMap addrRangeMapOf(Expr e, ARMCache &cache,
                            expr::PtrTypeCheckCache &ptCache) {
  seahorn::ScopedStats _st("hybrid.arm_build");
  return s_addrRangeMapOf(e, cache, ptCache);
}

AddrRangeMap mkARMBot() { return AddrRangeMap({}, false, true); }

AddrRangeMap mkARMTop() { return AddrRangeMap({}, true, false); }

bool approxPtrInRangeCheck(Expr p, unsigned s, Expr q, ARMCache &c,
                           expr::PtrTypeCheckCache &ptc) {
  AddrRangeMap pA = addrRangeMapOf(p, c, ptc);
  AddrRangeMap psA = pA;
  psA.addRange(AddrRange(s, s));
  AddrRangeMap qA = addrRangeMapOf(q, c, ptc);

  AddrRangeMap ppsA = addrRangeMapUnion(pA, psA);
  return !addrRangeMapIntersect(qA, ppsA).isAllBot();
}

bool approxPtrEq(Expr p, Expr q, ARMCache &c, PtrTypeCheckCache &ptc) {
  AddrRangeMap armP = addrRangeMapOf(p, c, ptc);
  AddrRangeMap armQ = addrRangeMapOf(q, c, ptc);
  // AG: XXX: Computes full intersection, but only Yes/No is used. Can speed up.
  AddrRangeMap intrs = addrRangeMapIntersect(armP, armQ);
  bool res = !intrs.isAllBot();
  if (!res) {
    LOG("hybrid.skip", WARN << *p << " != " << *q << "\n";);
    LOG("hybrid.skip", INFO << armP << " != \n" << armQ << "\n";);
  }
  return res;
}

}; // namespace addrRangeMap
}; // namespace expr
