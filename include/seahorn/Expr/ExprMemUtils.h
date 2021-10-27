#pragma once
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

/** Util functions and visitors for Expr trees representing memory **/

using namespace expr;

struct AddrRange
{
  unsigned low;
  unsigned high;
  bool isTop;
  AddrRange() : low(0), high(0), isTop(false) {}
  AddrRange(unsigned low, unsigned high, bool top=false) : low(low), high(high), isTop(top) {}
  AddrRange(const AddrRange &o) : low(o.low), high(o.high), isTop(o.isTop) {}

  bool contains(unsigned offset) {
    return isTop || (offset >= low && offset <= high);
  }
};


/** Given a base addr a, store upper and lower range being queried from.
 * E.g. ptr is ite(i, bvadd(a, u), bvsub(a, l)) =>
 * map => {a => (u, l)} **/
using MemAddrRangeMap = std::map<Expr, AddrRange>;

namespace expr {
namespace mem {
/** Returns true if e is either:
 * bvnum larger than 0xbf000000, or
 * terminal string starting with sea.sp0
 **/
bool isBaseAddr(Expr e);

namespace { /** building range of addresses from an expr tree **/
struct AR : public std::unary_function<Expr, VisitAction> {
  MemAddrRangeMap &arm;
  AR(MemAddrRangeMap &arm) : arm(arm) {}

  VisitAction operator()(Expr exp) {
    // reaching terminal, usually in explicit sp0
    if (isBaseAddr(exp)) {
      MemAddrRangeMap::const_iterator entry = arm.find(exp);
      if (entry == arm.end()) {
        arm.emplace(exp, AddrRange());
      }
      return VisitAction::skipKids();
    }
    // simple ptr arithmetics: add/sub(ptr, offset)
    // assume badd is flattened: bvadd(a, b, ..., n), where a, b, ... are
    // symbolic, n is numeric
    if (isOpX<BADD>(exp)) {
      Expr base, offset;
      for (auto b = exp->args_begin(), e = exp->args_end(); b != e; ++b) {
        /* try to find a base and an offset */
        if (base != NULL && offset != NULL)
          break;
        if (isBaseAddr(*b)) {
          base = *b;
          continue;
        }
        if (op::bv::is_bvnum(*b)) {
          offset = *b;
          continue;
        }
      }
      if (base == NULL || offset == NULL) {
        return VisitAction::doKids();
      }
      mpz_class offsetMpz = op::bv::toMpz(offset);
      auto offsetNum = offsetMpz.get_ui();
      MemAddrRangeMap::const_iterator entry = arm.find(base);
      if (entry != arm.end()) { /* already exist entry */
        auto range = entry->second;
        if (range.low == 0 && range.high == 0) {
          /* set first min and max */
          range.low = offsetNum;
          range.high = offsetNum;
        } else {
          /* attempt to update min and max */
          range.low = std::min((unsigned)offsetNum, range.low);
          range.high = std::max((unsigned)offsetNum, range.high);
        }
        arm[base] = range;
      } else {
        arm[base] = AddrRange(offsetNum, offsetNum, false);
      }
      return VisitAction::skipKids();
    }
    return VisitAction::doKids();
  }
};
} // end of namespace

inline void buildAddressRange(Expr mem, MemAddrRangeMap &arm) {
  AR ar(arm);
  dagVisit(ar, mem);
}
} // end of namespace mem
} // end of namespace expr