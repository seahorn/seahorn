#pragma once
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpCore.hh"


namespace expr{
namespace addrRangeMap{

struct AddrRange {
  unsigned low;
  unsigned high;
  bool isTop;
  AddrRange() : low(0), high(0), isTop(false) {}
  AddrRange(unsigned low, unsigned high, bool top = false)
      : low(low), high(high), isTop(top) {}
  AddrRange(const AddrRange &o) : low(o.low), high(o.high), isTop(o.isTop) {}

  bool contains(unsigned offset) {
    return isTop || (offset >= low && offset <= high);
  }

  /**
 * @brief Return new AddrRange that is aggregate of a and b
 * @param a(low_a, hi_a, isTop_a)
 * @param b(low_b, hi_b. isTop_b)
 * @return AddrRange(low_a + low_b, hi_a + hi_b, isTop_a|isTop_b)
 */
  AddrRange add(const AddrRange &o) {
    return AddrRange(low + o.low, high + o.high, isTop | o.isTop);
  }

  /** shorthand for add **/
  AddrRange operator+(const AddrRange &o) { return add(o); }

  /**
 * @brief Return new AddrRange that "joins" the ranges of a and b
 * to create a larger range
 * @param a(low_a, hi_a, isTop_a)
 * @param b(low_b, hi_b. isTop_b)
 * @return AddrRange(min(low_a, low_b), max(hi_a, hi_b), isTop_a|isTop_b)
 */
  AddrRange join(const AddrRange &o) {
    return AddrRange(std::min(low, o.low), std::max(high, o.high),
                     isTop | o.isTop);
  }

  /** shorthand for join **/
  AddrRange operator|(const AddrRange &o) { return join(o); }
};

/** Given a base addr a, store upper and lower range being queried from.
 * E.g. ptr is ite(i, bvadd(a, u), bvsub(a, l)) =>
 * map => {a => (u, l)} **/
using const_arm_iterator = std::map<Expr, AddrRange>::const_iterator;
using arm_iterator = std::map<Expr, AddrRange>::iterator;

/** Given a base addr a, store upper and lower range being queried from.
 * E.g. ptr is ite(i, bvadd(a, u), bvsub(a, l)) =>
 * map => {a => (u, l)} **/
class AddrRangeMap {
  std::map<Expr, AddrRange> m_rangeMap;
  bool m_isAllTop; /* {all => any} */
public:
  AddrRangeMap(std::map<Expr, AddrRange> rangeMap = {{}}, bool isAllTop = false)
      : m_rangeMap(rangeMap), m_isAllTop(isAllTop) {}
  AddrRangeMap(const AddrRangeMap &o)
      : m_rangeMap(o.m_rangeMap), m_isAllTop(o.m_isAllTop) {}

  /* access to internal map */
  AddrRange &operator[](const Expr &k) { return m_rangeMap[k]; }

  arm_iterator begin() { return m_rangeMap.begin(); }

  const_arm_iterator cbegin() { return m_rangeMap.cbegin(); }

  arm_iterator end() { return m_rangeMap.end(); }

  const_arm_iterator cend() { return m_rangeMap.cend(); }

  size_t count(Expr base) { return m_rangeMap.count(base); };

  /* modification and utility */

  /**
   * @brief Add range to all entries in arm
   * @param range
  */
  void addRange(const AddrRange &range);

  /**
  * @brief Return the union with o; colliding keys would take the min
  * and max of lower and uppper range
  * @param o
  * @return AddrRangeMap containing union of keys in both this and o with
  * updated ranges where necessary
  */
  AddrRangeMap unionWith(AddrRangeMap &o);

  /**
   * @brief returns whether (base, offset) is in current ARM
   * 
   * @param base: ptr base
   * @param offset: unsigned offset
   * @return true if this ARM is { all => top } or: base is a key in m_rangeMap
   * and offset is in m_rangeMap[base]
   * @return false otherwise
   */
  bool contains(Expr base, unsigned offset);

  /**
   * @brief whether this ARM is { all => top }
   */
  bool isAllTop() { return m_isAllTop; }

  /* printer */
  template <typename T> void print(T &OS) const;

  friend llvm::raw_ostream &operator<<(llvm::raw_ostream &OS,
                                       AddrRangeMap const &arm);

  friend std::ostream &operator<<(std::ostream &OS, AddrRangeMap const &arm);
};
} // namespace addrRangeMap

} // namespace expr
