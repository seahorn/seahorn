#pragma once
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include <limits>

namespace expr {

// AG XXX: why keys are ENode* and not Expr?
using PtrTypeCheckCache = std::unordered_map<ENode *, bool>;

namespace addrRangeMap {

class AddrRangeMap;
/// \brief An interval (range) of addresses
class AddrRange {
  unsigned m_low;
  unsigned m_high;
  friend class AddrRangeMap;

  void initTop() {
    m_low = std::numeric_limits<unsigned>::min();
    m_high = std::numeric_limits<unsigned>::max();
  }
  void initBot() {
    m_low = 1;
    m_high = 0;
  }

public:
  AddrRange() : m_low(0), m_high(0) {}
  AddrRange(unsigned low, unsigned high, bool top = false, bool bot = false)
      : m_low(low), m_high(high) {
    if (bot) {
      initBot();
    } else if (top) {
      initTop();
    }
  }
  AddrRange(const AddrRange &o) = default;
  AddrRange &operator=(const AddrRange &) = default;

  static AddrRange mkTop() { return AddrRange(0, 0, true, false); }
  static AddrRange mkBot() { return AddrRange(1, 0, false, true); }

  bool isTop() const {
    return m_low == std::numeric_limits<unsigned>::min() &&
           m_high == std::numeric_limits<unsigned>::max();
  }
  bool isBot() const { return m_low > m_high; }
  bool contains(unsigned offset) const {
    return isTop() || (!isBot() && (m_low <= offset && offset <= m_high));
  }

  /**
   * @brief Return new AddrRange that is aggregate of a and b
   * @param a(low_a, hi_a)
   * @param b(low_b, hi_b)
   * @return AddrRange(low_a + low_b, hi_a + hi_b)
   */
  AddrRange add(const AddrRange &o) const {
    if (isTop() || o.isTop())
      return mkTop();

    if (isBot() || o.isBot())
      return mkBot();

    return AddrRange(m_low + o.m_low, m_high + o.m_high, false, false);
  }

  /** shorthand for add **/
  AddrRange operator+(const AddrRange &o) const { return add(o); }

  /**
   * @brief Return new AddrRange that "joins" the ranges of a and b
   * to create a larger range
   * @param a(low_a, hi_a, kind_a)
   * @param b(low_b, hi_b, kind_b)
   * @return AddrRange(min(low_a, low_b), max(hi_a, hi_b), kind_a | kind_b)
   */
  AddrRange join(const AddrRange &o) const {
    if (isTop() || o.isTop())
      return mkTop();
    if (isBot())
      return o;
    if (o.isBot())
      return *this;

    return AddrRange(std::min(m_low, o.m_low), std::max(m_high, o.m_high),
                     false, false);
  }

  /** shorthand for join **/
  AddrRange operator|(const AddrRange &o) const { return join(o); }

  /**
   * @brief Returns new AddrRange that overlaps this and o; if this and o
   * does not overlap, return bot
   * @param o
   * @return AddrRange
   */
  AddrRange meet(const AddrRange &o) const {
    if (o.isTop())
      return *this;
    if (isTop())
      return o;

    if (isBot() || o.isBot())
      return mkBot();

    return AddrRange(std::max(m_low, o.m_low), std::min(m_high, o.m_high));
  }

  /* shorthand for overlap */
  AddrRange operator&(const AddrRange &o) const { return meet(o); }

  bool isValid() const;

  /// Zero Least Significant Bits
  AddrRange zeroLSB(size_t bits) {
    if (isBot() || isTop())
      return *this;

    unsigned mask = ~0;
    mask <<= bits;
    return AddrRange(m_low & mask, m_high & mask, false, false);
  }
};

inline AddrRange mkAddrRangeBot(void) { return AddrRange::mkBot(); }

inline AddrRange mkAddrRangeTop() { return AddrRange::mkTop(); }

/**
 * @brief zero the last n bits of low and high
 *
 * @param r range to zero bits
 * @param n number of bits to zero out
 * @return AddrRange with both low and high last n bits zeroed
 */
inline AddrRange zeroBitsRange(AddrRange &r, size_t n) {
  return r.zeroLSB(n);
}

/** Given a base addr a, store upper and lower range being queried from.
 * E.g. ptr is ite(i, bvadd(a, u), bvsub(a, l)) =>
 * map => {a => (u, l)} **/
class AddrRangeMap {
public:
  /** Given a base addr a, store upper and lower range being queried from.
   * E.g. ptr is ite(i, bvadd(a, u), bvsub(a, l)) =>
   * map => {a => (u, l)} **/
  using arm_range_map_t = std::unordered_map<Expr, AddrRange>;
  using const_arm_iterator = arm_range_map_t::const_iterator;
  using arm_iterator = arm_range_map_t::iterator;

private:
  arm_range_map_t m_rangeMap;
  bool m_isTop;
  bool m_isBot;

public:
  AddrRangeMap(const arm_range_map_t &rangeMap = {}, bool isTop = false,
               bool isBot = false)
      : m_rangeMap(rangeMap), m_isTop(isTop), m_isBot(isBot) {}
  AddrRangeMap(const AddrRangeMap &) = default;
  AddrRangeMap(AddrRangeMap &&) = default;

  AddrRangeMap &operator=(AddrRangeMap &&) = default;
  AddrRangeMap &operator=(const AddrRangeMap &) = default;

  /* access to internal map */
  AddrRange &operator[](const Expr &k) { return m_rangeMap[k]; }
  AddrRange at(const Expr &k) const { return m_rangeMap.at(k); }

  arm_iterator begin() { return m_rangeMap.begin(); }
  arm_iterator end() { return m_rangeMap.end(); }

  const_arm_iterator cbegin() const { return m_rangeMap.cbegin(); }
  const_arm_iterator cend() const { return m_rangeMap.cend(); }

  size_t count(const Expr &base) { return m_rangeMap.count(base); };
  arm_iterator find(const Expr &k) { return m_rangeMap.find(k); }
  const_arm_iterator find(const Expr &k) const { return m_rangeMap.find(k); }

  size_t size() const { return m_rangeMap.size(); }

  bool isValid() const;

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
  bool isAllTop() const { return m_isTop; }

  bool isAllBot() const { return m_isBot; }

  void setTop(bool v) { m_isTop = v; }

  void setBot(bool v) { m_isBot = v; }

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
