#pragma once
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include <limits>

namespace expr {
// AG XXX: why keys are ENode* and not Expr?
using PtrTypeCheckCache = std::unordered_map<ENode *, bool>;
namespace addrRangeMap {

struct AddrRange {
  unsigned m_low;
  unsigned m_high;
  bool m_isTop;
  bool m_isBot;
  AddrRange() : m_low(0), m_high(0), m_isTop(false), m_isBot(false) {}
  AddrRange(unsigned low, unsigned high, bool top = false, bool bot = false)
      : m_low(low), m_high(high), m_isTop(top), m_isBot(bot) {}
  AddrRange(const AddrRange &o) = default;
  AddrRange &operator=(const AddrRange &) = default;

  bool contains(unsigned offset) {
    return !m_isBot && (m_isTop || (m_low <= offset && offset <= m_high));
  }

  /**
   * @brief Return new AddrRange that is aggregate of a and b
   * @param a(low_a, hi_a)
   * @param b(low_b, hi_b)
   * @return AddrRange(low_a + low_b, hi_a + hi_b)
   */
  AddrRange add(const AddrRange &o) {
    bool top = m_isTop || o.m_isTop;
    bool bot = m_isBot && o.m_isBot;
    unsigned newLow = m_low + o.m_low, newHigh = m_high + o.m_high;
    if (top) {
      newLow = std::numeric_limits<unsigned>::min();
      newHigh = std::numeric_limits<unsigned>::max();
    }
    if (m_isBot) {
      newLow = o.m_low, newHigh = o.m_high;
    } else if (o.m_isBot) {
      newLow = m_low, newHigh = m_high;
    }
    return AddrRange(newLow, newHigh, top, bot);
  }

  /** shorthand for add **/
  AddrRange operator+(const AddrRange &o) { return add(o); }

  /**
   * @brief Return new AddrRange that "joins" the ranges of a and b
   * to create a larger range
   * @param a(low_a, hi_a, kind_a)
   * @param b(low_b, hi_b, kind_b)
   * @return AddrRange(min(low_a, low_b), max(hi_a, hi_b), kind_a | kind_b)
   */
  AddrRange join(const AddrRange &o) {
    bool top = m_isTop || o.m_isTop;
    bool bot = m_isBot && o.m_isBot;
    return AddrRange(std::min(m_low, o.m_low), std::max(m_high, o.m_high), top,
                     bot);
  }

  /** shorthand for join **/
  AddrRange operator|(const AddrRange &o) { return join(o); }

  /**
   * @brief Returns new AddrRange that overlaps this and o; if this and o
   * does not overlap, return bot
   * @param o
   * @return AddrRange
   */
  AddrRange meet(const AddrRange &o) {
    bool top = m_isTop && o.m_isTop;
    bool bot = m_isBot || o.m_isBot;
    unsigned newHigh = std::min(m_high, o.m_high);
    unsigned newLow = std::max(m_low, o.m_low);
    if (newHigh < newLow) {
      bot = true, top = false;
      newLow = std::numeric_limits<unsigned>::max(),
      newHigh = std::numeric_limits<unsigned>::min();
    }
    return AddrRange(newLow, newHigh, top, bot);
  }

  /* shorthand for overlap */
  AddrRange operator&(const AddrRange &o) { return meet(o); }

  bool isValid();
};

inline AddrRange mkAddrRangeBot(void) {
  return AddrRange(std::numeric_limits<unsigned>::max(),
                   std::numeric_limits<unsigned>::min(), false, true);
}

inline AddrRange mkAddrRangeTop() {
  return AddrRange(std::numeric_limits<unsigned>::min(),
                   std::numeric_limits<unsigned>::max(), true, false);
}


/**
 * @brief zero the last n bits of low and high
 *
 * @param r range to zero bits
 * @param n number of bits to zero out
 * @return AddrRange with both low and high last n bits zeroed
 */
AddrRange zeroBitsRange(AddrRange &r, size_t n);

/** Given a base addr a, store upper and lower range being queried from.
 * E.g. ptr is ite(i, bvadd(a, u), bvsub(a, l)) =>
 * map => {a => (u, l)} **/
using arm_range_map_t = std::unordered_map<Expr, AddrRange>;
using const_arm_iterator = arm_range_map_t::const_iterator;
using arm_iterator = arm_range_map_t::iterator;

/** Given a base addr a, store upper and lower range being queried from.
 * E.g. ptr is ite(i, bvadd(a, u), bvsub(a, l)) =>
 * map => {a => (u, l)} **/
class AddrRangeMap {
  arm_range_map_t m_rangeMap;
  bool m_isTop;
  bool m_isBot;

public:
  AddrRangeMap(arm_range_map_t rangeMap = {}, bool isTop = false,
               bool isBot = false)
      : m_rangeMap(rangeMap), m_isTop(isTop), m_isBot(isBot) {}
  AddrRangeMap(const AddrRangeMap &o) = default;
  AddrRangeMap &operator=(const AddrRangeMap &) = default;

  /* access to internal map */
  AddrRange &operator[](const Expr &k) { return m_rangeMap[k]; }

  arm_iterator begin() { return m_rangeMap.begin(); }
  arm_iterator end() { return m_rangeMap.end(); }

  const_arm_iterator cbegin() { return m_rangeMap.cbegin(); }
  const_arm_iterator cend() { return m_rangeMap.cend(); }

  size_t count(Expr base) { return m_rangeMap.count(base); };

  arm_iterator find(const Expr &k) { return m_rangeMap.find(k); }

  size_t size() { return m_rangeMap.size(); }

  bool isValid();

  /* modification and utility */

  /**
   * @brief Add range to all entries in arm
   * @param range
   */
  void addRange(const AddrRange &range);

  /**
   * @brief zero last n bits for all range in arm
   *
   * @param n number of bits to zero
   */
  void zeroBits(size_t n);

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
  bool isAllTop() { return m_isTop; }

  bool isAllBot() { return m_isBot; }

  void setTop(bool t) { m_isTop = t; }

  void setBot(bool t) { m_isBot = t; }

  /* printer */
  template <typename T> void print(T &OS) const;

  friend llvm::raw_ostream &operator<<(llvm::raw_ostream &OS,
                                       AddrRangeMap const &arm);

  friend std::ostream &operator<<(std::ostream &OS, AddrRangeMap const &arm);
};

// AG: XXX: Why keys are ENode* and not Expr?
using ARMCache = std::unordered_map<ENode *, AddrRangeMap>;

/**
 * @brief Given a ptr expression pE, build AddrRangeMap according to
 * type of pE:
 * - base addr: {pE => (0, 0)}
 * - bvadd(x, y): addrRangeMapOf(x) + addrRangeOf(y)
 * - ITE(c, x, y): addrRangeMapOf(x) | addrRangeMapOf(y), replace collidding
 * elements with larger range
 */
AddrRangeMap addrRangeMapOf(Expr pE, ARMCache &cache,
                            PtrTypeCheckCache &ptCache);

/**
 * @brief Given a num expression nE, build AddrRange according to
 * type of nE:
 * - num(n): {nE => (n, n)}
 * - sym(x): {nE => any} XXX: could use contextual infer
 * - bvadd(x, y): addrRangeOf(x) + addrRangeOf(y)
 * - ITE(c, x, y): addrRangeOf(x).join(addrRangeOf(y))
 */
AddrRange addrRangeOf(Expr nE);

/**
 * @brief Return the union of a and b; colliding keys would take union of
 * ranges
 * @param a
 * @param b
 * @return AddrRangeMap containing union of keys in either a or b with
 * updated ranges where necessary
 */
AddrRangeMap addrRangeMapUnion(AddrRangeMap &a, AddrRangeMap &b);

/**
 * @brief Return the intersection of a and b; colliding keys take the
 * intersections of ranges
 * @param a
 * @param b
 * @return AddrRangeMap containing intersection of keys in both a and b
 * with updated ranges
 */
AddrRangeMap addrRangeMapIntersect(AddrRangeMap &a, AddrRangeMap &b);

AddrRangeMap mkARMTop();

AddrRangeMap mkARMBot();

/**
 * @brief return true if p <= q <= p + s, over-approximate using ARM
 * @param p pointer expression marking start of a range
 * @param s offset from p
 * @param q pointer expression to check if it's in between range
 * @param c cache for building arm
 * @param ptc cache for ad-hoc type checking ptrs
 * @return false (α(p) ⊔ α(p + s)) ⊓ α(q) = ⊥
 * @return otherwise
 */
bool approxPtrInRangeCheck(Expr p, unsigned s, Expr q, ARMCache &c,
                           PtrTypeCheckCache &ptc);

bool approxPtrEq(Expr p, Expr q, ARMCache &c, PtrTypeCheckCache &ptc);

} // namespace addrRangeMap

} // namespace expr
