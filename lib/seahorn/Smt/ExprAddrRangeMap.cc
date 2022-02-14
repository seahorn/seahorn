#include "seahorn/Expr/ExprAddrRangeMap.hh"

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

}; // namespace addrRangeMap
}; // namespace expr