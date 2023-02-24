#include "seahorn/Expr/ExprRewriterDefs.hh"
#include "seahorn/Expr/ExprNumericUtils.hh"
#include "seahorn/Expr/ExprVisitor.hh"
#include "seahorn/Support/Stats.hh"
#include "llvm/Support/CommandLine.h"

static llvm::cl::opt<bool>
    UseArm("horn-hybrid-use-arm",
           llvm::cl::desc("Use ARM abstraction to simplify mem expr"),
           llvm::cl::init(false));

namespace expr {
using namespace addrRangeMap;
namespace utils {
bool shouldCache(const Expr &e) {
  if (isOpX<SELECT>(e) || isOpX<STORE>(e) || isOpX<ITE>(e)) {
    return true; // aggressive cache row and wow
  }
  return e->use_count() > 1;
}

} // namespace utils

bool ITECompRewriteConfig::shouldRewrite(const Expr &exp) const {
  return isOpX<ITE>(exp) || isOpX<CompareOp>(exp) || isOpX<BoolOp>(exp) ||
         isOpX<SELECT>(exp) || isOpX<BADD>(exp);
}

RewriteResult ITECompRewriteConfig::doRewrite(const Expr &exp) {
  RewriteResult res = {exp, RWStatus::RW_DONE};
  if (isOpX<ITE>(exp)) {
    res = m_iteRule(exp);
  } else if (isOpX<CompareOp>(exp)) {
    res = m_compRule(exp);
  } else if (isOpX<BoolOp>(exp)) {
    res = m_boolRule(exp);
  } else if (isOpX<SELECT>(exp)) {
    res = m_arrayRule(exp);
  } else if (isOpX<BADD>(exp)) {
    res = m_arithRule(exp);
  }
  return res;
}

bool PointerArithmeticConfig::shouldRewrite(const Expr &exp) const {
  return isOpX<BADD>(exp) || isOpX<ITE>(exp);
}

RewriteResult PointerArithmeticConfig::doRewrite(const Expr &exp) {
  if (isOpX<BADD>(exp)) {
    return m_arithRule(exp);
  }
  return {exp, RWStatus::RW_DONE};
}

bool WriteOverWriteConfig::shouldRewrite(const Expr &e) {
  return isOpX<STORE>(e) || isOpX<STORE_MAP>(e) || isOpX<ITE>(e) ||
         isOpX<BADD>(e);
}

RewriteResult WriteOverWriteConfig::doRewrite(const Expr &exp) {
  if (isOpX<BADD>(exp)) {
    return m_arithRule(exp);
  } else if (isOpX<STORE>(exp) || isOpX<STORE_MAP>(exp)) {
    return m_wowRule(exp);
  }
  return {exp, RWStatus::RW_DONE};
}

void WriteOverWriteConfig::onAfterRewrite(const Expr &oldE, const Expr &newE) const {
  if (isOpX<STORE_MAP>(oldE) && isOpX<STORE_MAP>(newE) && oldE != newE) {
    op::array::transferStoreMapCache(&*oldE, &*newE, m_wowRule.m_smapC);
  }
}

RewriteResult ReadOverWriteRule::operator()(const Expr &exp) const {
  if (!isOpX<SELECT>(exp)) {
    return {exp, RWStatus::RW_SKIP};
  }
  const Expr &arr = exp->arg(0);
  const Expr &idx = exp->arg(1);

  // XXX make this optional, it is potentially costly but only used for stats
  if (!isOpX<ITE>(arr) && m_cache.find(&*exp) == m_cache.end()) {
    if (isOpX<STORE_MAP>(arr)) {
      auto nRows = op::array::storeMapGetMap(arr)->arity();
      seahorn::Stats::uset("hybrid.read_over_writes",
                           seahorn::Stats::get("hybrid.read_over_writes") +
                               nRows);
    } else {
      seahorn::Stats::count("hybrid.read_over_writes");
    }
  }

  // Read-over-write/ite: push select down to leaves
  if (isOpX<STORE>(arr)) {
    return rewriteReadOverStore(arr, idx);
  } else if (isOpX<ITE>(arr)) {
    return rewriteReadOverIte(arr, idx);
  } else if (isOpX<MEMSET_WORDS>(arr)) {
    return rewriteReadOverMemset(arr, idx);
  } else if (isOpX<MEMCPY_WORDS>(arr)) {
    return rewriteReadOverMemcpy(arr, idx);
  } else if (isOpX<STORE_MAP>(arr)) {
    return rewriteReadOverStoreMap(arr, idx);
  } else {
    return {exp, RWStatus::RW_DONE};
  }
}

RewriteResult ReadOverWriteRule::rewriteReadOverStore(const Expr &arr, const Expr &idx) const {
  const Expr &arrN = op::array::storeArray(arr);
  const Expr &idxN = op::array::storeIdx(arr);
  Expr res = mk<ITE>(mk<EQ>(idx, idxN), op::array::storeVal(arr),
                     op::array::select(arrN, idx));
  return {std::move(res), RWStatus::RW_2};
}

RewriteResult ReadOverWriteRule::rewriteReadOverIte(const Expr &arr, const Expr &idx) const {
  const Expr &i = arr->arg(0);
  const Expr &t = arr->arg(1);
  const Expr &e = arr->arg(2);
  Expr res = mk<ITE>(i, op::array::select(t, idx), op::array::select(e, idx));
  return {std::move(res), RWStatus::RW_2};
}

RewriteResult ReadOverWriteRule::rewriteReadOverMemset(const Expr &arr, const Expr &idx) const {
  const Expr &inMem = arr->arg(0);
  const Expr &idxN = arr->arg(1);
  const Expr &len = arr->arg(2);
  const Expr &val = arr->arg(3);

  ExprFactory &efac = arr->efac();
  Expr res;

  if (op::bv::is_bvnum(len)) {
    unsigned cLen = bv::toMpz(len).get_ui() - m_wordSize;
    Expr offset = op::bv::bvnum(cLen, op::bv::widthBvNum(len), efac);
    Expr last = utils::ptrAdd(idxN, offset);
    // idxN <= idx <= idxN + sz
    Expr cmp = utils::ptrInRangeCheck(idxN, idx, last);
    Expr otherVal = op::array::select(inMem, idx);
    if (UseArm &&
        !approxPtrInRangeCheck(idxN, cLen, idx, m_armCache, m_ptCache)) {
      /* idx is for sure not in range of [idxN, idxN + sz] */
      seahorn::Stats::count("hybrid.arm_skip_memset");
      return {std::move(otherVal), RWStatus::RW_1};
    }
    res = mk<ITE>(cmp, val, otherVal);
  } else {
    Expr wordSzE = op::bv::bvnum(m_wordSize, m_ptrWidth, len->efac());
    Expr last = utils::ptrSub(utils::ptrAdd(idxN, len), wordSzE);
    // idxN <= idx <= idxN + sz
    Expr cmp = utils::ptrInRangeCheck(idxN, idx, last);
    Expr otherVal = op::array::select(inMem, idx);
    if (UseArm && !approxPtrEq(idx, idxN, m_armCache, m_ptCache)) {
      seahorn::Stats::count("hybrid.arm_skip_memset");
      return {std::move(otherVal), RWStatus::RW_1};
    }
    res = mk<ITE>(cmp, val, otherVal);
  }
  return {std::move(res), RWStatus::RW_2};
}

Expr ReadOverWriteRule::revertSMapToIte(const Expr &storeMap, const Expr &idx) const {
  const Expr &arr = storeMap->arg(0);
  const Expr &base = storeMap->arg(1);
  const Expr &consList = storeMap->arg(2);

  Stats::count("hybrid.smap_revert_ite");

  Expr res = arr;
  auto it = m_smapCache.find(&*storeMap);
  if (it != m_smapCache.end()) {
    op::array::OffsetValueMap *cached = it->second;
    for (auto ovIt = cached->cbegin(); ovIt != cached->cend(); ovIt++) {
      Expr oIdx =
          mk<BADD>(base, op::bv::bvnum(ovIt->first, m_ptrWidth, base->efac()));
      res = op::array::store(res, oIdx, ovIt->second);
    }
    res = op::array::select(res, idx);
    return res;
  }

  // Fallback to stored cons list, re-build cache
  Stats::count("hybrid.smap_revert_ite_fallback");
  op::array::OffsetValueMap *ovM = new op::array::OffsetValueMap();
  Expr head = consList;
  while (head) {
    Expr ov = head->arg(0);
    head = head->arity() == 2 ? head->arg(1) : nullptr;
    unsigned long oXNum = op::bv::toMpz(ov->arg(0)).get_ui();
    if (ovM->find(oXNum) == ovM->cend()) { // keep latest value only
      ovM->insert({oXNum, ov->arg(1)});
      Expr oIdx = mk<BADD>(base, ov->arg(0));
      res = op::array::store(res, oIdx, ov->arg(1));
    }
  }
  res = op::array::select(res, idx);
  // XXX check for potential issue with reference counting, what if
  // XXX storeMap was already in the cache. Then Ref() will double count.
  storeMap->Ref();
  m_smapCache.insert({&*storeMap, ovM});
  return res;
}

RewriteResult ReadOverWriteRule::rewriteReadOverStoreMap(const Expr &arr, const Expr &idx) const {
  Expr nxtArr = arr->arg(0), base = arr->arg(1);
  Expr smap = op::array::storeMapGetMap(arr);

  Expr idxBase, idxOffset;
  bool idxHasBase = isSingleBasePtr(idx, m_ptrWidth, idxBase, idxOffset);
  if (idxHasBase) {
    if (idxBase == base) {
      if (op::bv::is_bvnum(idxOffset)) {
        Expr val = op::array::storeMapFind(arr, idxOffset, m_smapCache);
        if (val) {
          // R-HIT
          Stats::count("hybrid.smap_hit");
          return {val, RWStatus::RW_DONE};
        } else {
          // R-MISS
          Stats::count("hybrid.smap_miss");
          return {op::array::select(nxtArr, idx), RWStatus::RW_1};
        }
      } else {
        // same base but symolic offset, can only abort
        Stats::count("hybrid.smap_abort");
        Expr res = revertSMapToIte(arr, idx);
        return {std::move(res), RWStatus::RW_FULL};
      }
    } else {
      // R-SKIP
      Stats::count("hybrid.smap_skip");
      return {op::array::select(nxtArr, idx), RWStatus::RW_1};
    }
  } else {
    // R-Abort
    Stats::count("hybrid.smap_abort");
    Expr res = revertSMapToIte(arr, idx);
    return {std::move(res), RWStatus::RW_FULL};
  }
}

RewriteResult ReadOverWriteRule::rewriteReadOverMemcpy(const Expr &arr, const Expr &idx) const {
  /** select(copy(a, p, b, q, s), i) =>
   * ITE(p ≤ i < p + s, read(b, q + (i − p)), read(a, i)) **/
  Expr res;
  Expr dstMem = arr->arg(0), srcMem = arr->arg(1);
  Expr dstIdx = arr->arg(2), srcIdx = arr->arg(3);
  Expr len = arr->arg(4);
  // idx within dstIdx + len => load from src + (idx - dstIdx)
  Expr dsOffset = utils::ptrSub(idx, dstIdx);
  Expr cpyIdx = utils::ptrAdd(srcIdx, dsOffset);
  // select(srcMem, dstIdx - srcIdx + idx)
  Expr cpyVal = op::array::select(srcMem, cpyIdx);
  if (op::bv::is_bvnum(len)) {
    unsigned cLen = bv::toMpz(len).get_ui() - m_wordSize;
    Expr offset = op::bv::bvnum(cLen, op::bv::widthBvNum(len), len->efac());
    Expr dstLast = utils::ptrAdd(dstIdx, offset);
    // dstIdx <= idx <= dstIdx + sz
    Expr cmp = utils::ptrInRangeCheck(dstIdx, idx, dstLast);
    // select(dstMem, idx)
    Expr dstOtherVal = op::array::select(dstMem, idx);
    if (UseArm &&
        !approxPtrInRangeCheck(dstIdx, cLen, idx, m_armCache, m_ptCache)) {
      /* idx is for sure not in range of [dstIdx, dstIdx + sz] */
      seahorn::Stats::count("hybrid.arm_skip_memcpy");
      return {dstOtherVal, RWStatus::RW_1};
    }
    res = mk<ITE>(cmp, cpyVal, dstOtherVal);
  } else {
    Expr wordSzE = op::bv::bvnum(m_wordSize, m_ptrWidth, len->efac());
    Expr dstLast = utils::ptrSub(utils::ptrAdd(dstIdx, len), wordSzE);
    // dstIdx <= idx <= dstIdx + sz
    Expr cmp = utils::ptrInRangeCheck(dstIdx, idx, dstLast);
    // select(dstMem, idx)
    Expr dstOtherVal = op::array::select(dstMem, idx);
    if (UseArm && !approxPtrEq(dstIdx, idx, m_armCache, m_ptCache)) {
      seahorn::Stats::count("hybrid.arm_skip_memcpy");
      return {dstOtherVal, RWStatus::RW_1};
    }
    res = mk<ITE>(cmp, cpyVal, dstOtherVal);
  }
  return {res, RWStatus::RW_2};
}
using namespace op::array;
using namespace op::bv;
RewriteResult WriteOverWriteRule::rewriteStore(const Expr &e) const {
  Expr arr = storeArray(e), idx = storeIdx(e), val = storeVal(e);
  /* idx should be normalised */
  Expr idxBase;
  Expr idxOffset;
  bool hasBase = isSingleBasePtr(idx, m_ptrWidth, idxBase, idxOffset);
  if (isOpX<STORE>(arr)) {
    Stats::count("hybrid.store_over_store");
    Expr arrNxt = storeArray(arr), idxNxt = storeIdx(arr),
         valNxt = storeVal(arr);
    Expr idxNxtBase, idxNxtOffset;
    bool nxtHasBase =
        isSingleBasePtr(idxNxt, m_ptrWidth, idxNxtBase, idxNxtOffset);
    if (hasBase && nxtHasBase) {
      /* both addresses have a base */
      if (idxBase == idxNxtBase) {
        if (is_bvnum(idxOffset) && is_bvnum(idxNxtOffset)) {
          /* b + x, b + y can be merged */
          if (op::bv::toMpz(idxOffset) == op::bv::toMpz(idxNxtOffset)) {
            /* edge case: offset == offsetNxt */
            seahorn::Stats::count("hybrid.store_erase");
            return {op::array::store(arrNxt, idx, val), RWStatus::RW_DONE};
          }
          /* SMAP-NEW */
          Expr res = storeMapNew(arrNxt, idxBase, op::strct::mk(idxOffset, val),
                                 op::strct::mk(idxNxtOffset, valNxt), m_smapC);
          Stats::count("hybrid.smap_new");
          return {res, RWStatus::RW_DONE}; // maybe commute
        }
      } else {
        /* STORE-COMMUTE */
        if (expr::mem::getBasedAddrSerial(idxBase) <
            expr::mem::getBasedAddrSerial(idxNxtBase)) {
          Expr newNxtStore = op::array::store(arrNxt, idx, val);
          Expr newStore = op::array::store(newNxtStore, idxNxt, valNxt);
          seahorn::Stats::count("hybrid.store_store_commute");
          return {newStore, RWStatus::RW_2};
        }
      }
    }
  } else if (isOpX<STORE_MAP>(arr)) {
    Stats::count("hybrid.store_over_storemap");
    Expr sMapArr = arr->arg(0);
    Expr sMapBase = arr->arg(1);
    Expr sMap = storeMapGetMap(arr);
    if (hasBase) {
      if (sMapBase == idxBase && is_bvnum(idxOffset)) {
        /* SMAP-HIT */
        Expr res = storeMapInsert(arr, op::strct::mk(idxOffset, val), m_smapC);
        Stats::count("hybrid.smap_insert");
        return {res, RWStatus::RW_DONE};
      } else if (expr::mem::getBasedAddrSerial(idxBase) <
                 expr::mem::getBasedAddrSerial(sMapBase)) {
        /* SMAP-COMMUTE */
        seahorn::Stats::count("hybrid.store_smap_commute");
        Expr sMapArr = arr->arg(0);
        Expr sMapBase = arr->arg(1);
        Expr sMap = storeMapGetMap(arr);

        Expr innerStore = e->efac().mkTern(e->op(), sMapArr, idx, val);
        Expr res = arr->efac().mkTern(arr->op(), innerStore, sMapBase, sMap);
        op::array::transferStoreMapCache(&*arr, &*res, m_smapC);
        return {res, RWStatus::RW_2};
      }
    }
  }
  return {e, RWStatus::RW_DONE};
}

RewriteResult WriteOverWriteRule::operator()(const Expr &e) const {
  if (!isOpX<STORE>(e) && !isOpX<STORE_MAP>(e)) {
    return {e, RWStatus::RW_SKIP};
  }
  if (isOpX<STORE>(e)) {
    return rewriteStore(e);
  } else { // all handled during store
    return {e, RWStatus::RW_DONE};
  }
}

RewriteResult CompareRewriteRule::operator()(const Expr &exp) const {
  if (!isOpX<CompareOp>(exp)) {
    return {exp, RWStatus::RW_SKIP};
  }
  Expr lhs = exp->left();
  Expr rhs = exp->right();

  /* a op b comp a op c ==> b comp c
    e.g. (a - b) == (a - c) ==> b == c
  */
  if (isOpX<BvOp>(lhs) && lhs->op() == rhs->op() &&
      lhs->arity() == rhs->arity() && lhs->arity() == 2) {
    if (lhs->arg(0) == rhs->arg(0)) {
      Expr res = m_efac.mkBin(exp->op(), lhs->arg(1), rhs->arg(1));
      return {res, RWStatus::RW_1};
    }
    if (lhs->arg(1) == rhs->arg(1)) {
      Expr res = m_efac.mkBin(exp->op(), lhs->arg(0), rhs->arg(0));
      return {res, RWStatus::RW_1};
    }
  }
  // a == a => true, only works if a is constant bvnum
  if (isOpX<EQ>(exp)) {
    bool bothNum = op::bv::is_bvnum(lhs) && op::bv::is_bvnum(rhs);
    if (bothNum) {
      return {op::bv::toMpz(lhs) == op::bv::toMpz(rhs) ? trueE : falseE,
              RWStatus::RW_DONE};
    }
    Expr rBase, rOffset, lBase, lOffset;
    bool rHasBase = isSingleBasePtr(rhs, m_ptrWidth, rBase, rOffset);
    bool lHasBase = isSingleBasePtr(lhs, m_ptrWidth, lBase, lOffset);
    if (rHasBase && lHasBase) {
      if (rBase == lBase) {
        // compare offset
        return {mk<EQ>(lOffset, rOffset), RWStatus::RW_1};
      } else {
        // diff base => diff pointer
        seahorn::Stats::count("hybrid.thm_skip_store");
        return {falseE, RWStatus::RW_DONE};
      }
    }
    if (UseArm && isPtrExpr(lhs, m_ptcCache) && isPtrExpr(rhs, m_ptcCache)) {
      if (!approxPtrEq(lhs, rhs, m_armCache, m_ptcCache)) {
        seahorn::Stats::count("hybrid.arm_skip_store");
        return {falseE, RWStatus::RW_DONE};
      }
    }
  }

  // normalize neq: a != b ==> !(a=b)
  if (isOpX<NEQ>(exp)) {
    Expr negation = mk<EQ>(lhs, rhs);
    return {mk<NEG>(negation), RWStatus::RW_2};
  }
  return {exp, RWStatus::RW_DONE};
}

RewriteResult ITERewriteRule::operator()(const Expr &exp) const {
  if (!isOpX<ITE>(exp)) {
    return {exp, RWStatus::RW_SKIP};
  }

  Expr i = exp->arg(0);
  Expr t = exp->arg(1);
  Expr e = exp->arg(2);
  // ite(a, true, false) => a
  if (isOpX<TRUE>(t) && isOpX<FALSE>(e)) {
    return {i, RWStatus::RW_DONE};
  }
  // ite(a, false, true) => !a
  if (isOpX<FALSE>(t) && isOpX<TRUE>(e)) {
    return {mk<NEG>(i), RWStatus::RW_1}; // simp dbl negation
  }
  // ite(i, a, a) => a
  if (t == e) {
    return {t, RWStatus::RW_DONE};
  }
  // ite(a, b, ite(!a, c, d)) => ite(a, b, c)
  if (isOpX<ITE>(e)) {
    Expr e_i = e->arg(0);
    Expr e_t = e->arg(1);
    if (op::boolop::areNegations(i, e_i)) {
      return {mk<ITE>(i, t, e_t), RWStatus::RW_1};
    }
  }
  // ite(true, a, b) => a
  if (isOpX<TRUE>(i)) {
    return {t, RWStatus::RW_DONE};
  }
  // ite(false, a, b) => b
  if (isOpX<FALSE>(i)) {
    return {e, RWStatus::RW_DONE};
  }
  return {exp, RWStatus::RW_DONE};
}

} // namespace expr
