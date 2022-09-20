#include "seahorn/Expr/ExprRewriter.hh"
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

bool isMemWriteOp(Expr e) {
  return isOpX<STORE>(e) || isOpX<ITE>(e) || isOpX<MEMSET_WORDS>(e) ||
         isOpX<MEMCPY_WORDS>(e) || isOpX<STORE_MAP>(e);
}
} // namespace utils

bool ITECompRewriteConfig::shouldRewrite(Expr exp) {
  // return isOpX<ITE>(exp) || isOpX<CompareOp>(exp) || isOpX<BoolOp>(exp) ||
  //        isOpX<SELECT>(exp) || isOpX<BADD>(exp);
  return isOpX<ITE>(exp) || isOpX<SELECT>(exp) || isOpX<CompareOp>(exp);
}

rewrite_result ITECompRewriteConfig::applyRewriteRules(Expr exp) {
  rewrite_result res = {exp, rewrite_status::RW_DONE};
  if (isOpX<ITE>(exp)) {
    res = m_iteRule(exp);
  } else if (isOpX<CompareOp>(exp)) {
    res = m_compRule(exp);
  } else if (isOpX<BoolOp>(exp)) {
    // res = m_boolRule(exp);
  } else if (isOpX<SELECT>(exp)) {
    res = m_arrayRule(exp);
  } else if (isOpX<BADD>(exp)) {
    // res = m_arithRule(exp);
  }
  return res;
}

bool PointerArithmeticConfig::shouldRewrite(Expr exp) {
  return isOpX<BADD>(exp) || isOpX<ITE>(exp);
}

rewrite_result PointerArithmeticConfig::applyRewriteRules(Expr exp) {
  rewrite_result res = {exp, rewrite_status::RW_DONE};
  if (isOpX<BADD>(exp)) {
    res = m_arithRule(exp);
  }
  return res;
}

bool WriteOverWriteConfig::shouldRewrite(Expr e) {
  return isOpX<STORE>(e) || isOpX<STORE_MAP>(e) || isOpX<ITE>(e) ||
         isOpX<BADD>(e);
}

rewrite_result WriteOverWriteConfig::applyRewriteRules(Expr exp) {
  rewrite_result res = {exp, rewrite_status::RW_DONE};
  if (isOpX<BADD>(exp)) {
    res = m_arithRule(exp);
  } else if (isOpX<STORE>(exp) || isOpX<STORE_MAP>(exp)) {
    res = m_wowRule(exp);
  }
  return res;
}

rewrite_result ReadOverWriteRule::operator()(Expr exp) {
  if (!isOpX<SELECT>(exp)) {
    return {exp, rewrite_status::RW_SKIP};
  }
  Expr arr = exp->arg(0);
  Expr idx = exp->arg(1);
  if (!isOpX<ITE>(arr) && m_cache.find(&*exp) == m_cache.end()) {
    if (isOpX<STORE_MAP>(arr)) {
      size_t nRows = op::array::storeMapGetMap(arr)->arity();
      seahorn::Stats::uset("hybrid.read_over_writes",
                           seahorn::Stats::get("hybrid.read_over_writes") +
                               nRows);
    } else {
      seahorn::Stats::count("hybrid.read_over_writes");
    }
  }
  /** Read-over-write/ite: push select down to leaves
   **/
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
    return {exp, rewrite_status::RW_DONE};
  }
}

rewrite_result ReadOverWriteRule::rewriteReadOverStore(Expr arr, Expr idx) {
  seahorn::ScopedStats _st("rw_ro_store");
  Expr arrN = op::array::storeArray(arr);
  Expr idxN = op::array::storeIdx(arr);
  // if (UseArm) {
  //   if (!approxPtrEq(idx, idxN, m_armCache,
  //                    m_ptCache)) { /* idx!=idxN must be true*/
  //     seahorn::Stats::count("hybrid.arm_skip_store");
  //     return {op::array::select(arrN, idx), rewrite_status::RW_1};
  //   }
  // }
  Expr res = mk<ITE>(mk<EQ>(idx, idxN), op::array::storeVal(arr),
                     op::array::select(arrN, idx));
  return {res, rewrite_status::RW_2};
}

rewrite_result ReadOverWriteRule::rewriteReadOverIte(Expr arr, Expr idx) {
  seahorn::ScopedStats _st("rw_ro_ite");
  Expr i = arr->arg(0);
  Expr t = arr->arg(1);
  Expr e = arr->arg(2);
  Expr res = mk<ITE>(i, op::array::select(t, idx), op::array::select(e, idx));
  return {res, rewrite_status::RW_2};
}

rewrite_result ReadOverWriteRule::rewriteReadOverMemset(Expr arr, Expr idx) {
  seahorn::ScopedStats _st("rw_ro_memset");

  Expr inMem = arr->arg(0);
  Expr idxN = arr->arg(1);
  Expr len = arr->arg(2);
  Expr val = arr->arg(3);
  Expr res;
  if (op::bv::is_bvnum(len)) {
    unsigned cLen = bv::toMpz(len).get_ui() - m_wordSize;
    Expr offset = op::bv::bvnum(cLen, op::bv::widthBvNum(len), len->efac());
    Expr last = utils::ptrAdd(idxN, offset);
    // idxN <= idx <= idxN + sz
    Expr cmp = utils::ptrInRangeCheck(idxN, idx, last);
    Expr otherVal = op::array::select(inMem, idx);
    if (UseArm &&
        !approxPtrInRangeCheck(idxN, cLen, idx, m_armCache, m_ptCache)) {
      /* idx is for sure not in range of [idxN, idxN + sz] */
      seahorn::Stats::count("hybrid.arm_skip_memset");
      return {otherVal, rewrite_status::RW_1};
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
      return {otherVal, rewrite_status::RW_1};
    }
    res = mk<ITE>(cmp, val, otherVal);
  }
  return {res, rewrite_status::RW_2};
}

bool ReadOverWriteRule::revertSMapToIte(Expr arr, Expr base, Expr smap,
                                        Expr idx, Expr &res) {
  bool canSkipFullRw = false;
  seahorn::ScopedStats _st("stmap_revert");
  Stats::count("hybrid.stmap_revert_ite");
  res = op::array::select(arr, idx);
  auto cit = cache.find(&*res);
  if (cit != cache.end()) {
    Stats::count("hybrid.stmap_revert_ite_skip_full_rewrite");
    res = cit->second;
    canSkipFullRw = true;
  }
  for (auto it = smap->args_begin(); it != smap->args_end(); it++) {
    Expr ov = *it;
    Expr oIdx = mk<BADD>(base, ov->arg(0));
    // if (UseArm && !approxPtrEq(oIdx, idx, m_armCache, m_ptCache)) {
    //   Stats::count("hybrid.arm_skip_store");
    //   continue; // idx!=oIdx
    // }
    res = mk<ITE>(mk<EQ>(idx, oIdx), ov->arg(1), res);
  }
  return canSkipFullRw;
}

rewrite_result ReadOverWriteRule::rewriteReadOverStoreMap(Expr arr, Expr idx) {
  seahorn::ScopedStats _st("rw_ro_stmap");
  Expr nxtArr = arr->arg(0), base = arr->arg(1);
  Expr smap = op::array::storeMapGetMap(arr);

  Expr idxBase, idxOffset;
  bool idxHasBase = isSingleBasePtr(idx, m_ptrWidth, idxBase, idxOffset);
  if (idxHasBase) {
    if (idxBase == base) {
      if (op::bv::is_bvnum(idxOffset)) {
        Expr val = op::array::storeMapFind(arr, idxOffset);
        if (val) {
          // R-HIT
          Stats::count("hybrid.smap_hit");
          return {val, rewrite_status::RW_DONE};
        } else {
          // R-MISS
          Stats::count("hybrid.smap_miss");
          return {op::array::select(nxtArr, idx), rewrite_status::RW_1};
        }
      } else {
        // same base but symolic offset, can only abort
        Stats::count("hybrid.smap_abort");
        Expr res;
        bool canSkipFullRw = revertSMapToIte(nxtArr, base, smap, idx, res);
        return {res, canSkipFullRw ? rewrite_status::RW_DONE
                                   : rewrite_status::RW_FULL};
      }
    } else {
      // R-SKIP
      Stats::count("hybrid.smap_skip");
      return {op::array::select(nxtArr, idx), rewrite_status::RW_1};
    }
  } else {
    // R-Abort
    Stats::count("hybrid.smap_abort");
    Expr res;
    bool canSkipFullRw = revertSMapToIte(nxtArr, base, smap, idx, res);
    return {res,
            canSkipFullRw ? rewrite_status::RW_DONE : rewrite_status::RW_FULL};
  }
}

rewrite_result ReadOverWriteRule::rewriteReadOverMemcpy(Expr arr, Expr idx) {
  seahorn::ScopedStats _st("rw_ro_memcpy");
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
      return {dstOtherVal, rewrite_status::RW_1};
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
      return {dstOtherVal, rewrite_status::RW_1};
    }
    res = mk<ITE>(cmp, cpyVal, dstOtherVal);
  }
  return {res, rewrite_status::RW_2};
}
using namespace op::array;
using namespace op::bv;
rewrite_result WriteOverWriteRule::rewriteStore(Expr e) {
  seahorn::ScopedStats _st("rw_wo_store");
  Expr arr = storeArray(e), idx = storeIdx(e), val = storeVal(e);
  /* idx should be normalised */
  Expr idxBase;
  Expr idxOffset;
  bool hasBase = isSingleBasePtr(idx, m_ptrWidth, idxBase, idxOffset);
  if (isOpX<STORE>(arr)) {
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
            return {op::array::store(arrNxt, idx, val),
                    rewrite_status::RW_DONE};
          }
          /* SMAP-NEW */
          ExprVector smap = {op::strct::mk(idxOffset, val),
                             op::strct::mk(idxNxtOffset, valNxt)};
          Expr res = storeMap<ExprVector, TUPLE>(arrNxt, idxBase, smap);
          Stats::count("hybrid.smap_new");
          return {res, rewrite_status::RW_DONE}; // maybe commute
        }
      } else {
        /* STORE-COMMUTE */
        if (expr::mem::getBasedAddrSerial(idxBase) <
            expr::mem::getBasedAddrSerial(idxNxtBase)) {
          Expr newNxtStore = op::array::store(arrNxt, idx, val);
          Expr newStore = op::array::store(newNxtStore, idxNxt, valNxt);
          seahorn::Stats::count("hybrid.store_store_commute");
          return {newStore, rewrite_status::RW_2};
        }
      }
    }
  } else if (isOpX<STORE_MAP>(arr)) {
    Expr sMapArr = arr->arg(0);
    Expr sMapBase = arr->arg(1);
    Expr sMap = storeMapGetMap(arr);
    if (hasBase) {
      if (sMapBase == idxBase && is_bvnum(idxOffset)) {
        /* SMAP-HIT */
        Expr res = storeMapInsert(arr, op::strct::mk(idxOffset, val));
        Stats::count("hybrid.smap_insert");
        return {res, rewrite_status::RW_DONE};
      } else if (expr::mem::getBasedAddrSerial(idxBase) <
                 expr::mem::getBasedAddrSerial(sMapBase)) {
        /* SMAP-COMMUTE */
        seahorn::Stats::count("hybrid.store_smap_commute");
        Expr sMapArr = arr->arg(0);
        Expr sMapBase = arr->arg(1);
        Expr sMap = storeMapGetMap(arr);

        Expr innerStore = e->efac().mkTern(e->op(), sMapArr, idx, val);
        Expr res = arr->efac().mkTern(arr->op(), innerStore, sMapBase, sMap);
        return {res, rewrite_status::RW_2};
      }
    }
  }
  return {e, rewrite_status::RW_DONE};
}

rewrite_result WriteOverWriteRule::operator()(Expr e) {
  if (!isOpX<STORE>(e) && !isOpX<STORE_MAP>(e)) {
    return {e, rewrite_status::RW_SKIP};
  }
  if (isOpX<STORE>(e)) {
    return rewriteStore(e);
  } else { // all handled during store
    return {e, rewrite_status::RW_DONE};
  }
}

rewrite_result CompareRewriteRule::operator()(Expr exp) {
  seahorn::ScopedStats _st("rw_comp");
  if (!isOpX<CompareOp>(exp)) {
    return {exp, rewrite_status::RW_SKIP};
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
      return {res, rewrite_status::RW_1};
    }
    if (lhs->arg(1) == rhs->arg(1)) {
      Expr res = m_efac.mkBin(exp->op(), lhs->arg(0), rhs->arg(0));
      return {res, rewrite_status::RW_1};
    }
  }
  // a == a => true, only works if a is constant bvnum
  if (isOpX<EQ>(exp)) {
    bool bothNum = op::bv::is_bvnum(lhs) && op::bv::is_bvnum(rhs);
    if (bothNum) {
      return {op::bv::toMpz(lhs) == op::bv::toMpz(rhs) ? trueE : falseE,
              rewrite_status::RW_DONE};
    }
    Expr rBase, rOffset, lBase, lOffset;
    bool rHasBase = isSingleBasePtr(rhs, m_ptrWidth, rBase, rOffset);
    bool lHasBase = isSingleBasePtr(lhs, m_ptrWidth, lBase, lOffset);
    if (rHasBase && lHasBase) {
      if (rBase == lBase) {
        // compare offset
        return {mk<EQ>(lOffset, rOffset), rewrite_status::RW_1};
      } else {
        // diff base => diff pointer
        seahorn::Stats::count("hybrid.thm_skip_store");
        return {falseE, rewrite_status::RW_DONE};
      }
    }
    if (UseArm && isPtrExpr(lhs, m_ptcCache) && isPtrExpr(rhs, m_ptcCache)) {
      if (!approxPtrEq(lhs, rhs, m_armCache, m_ptcCache)) {
        seahorn::Stats::count("hybrid.arm_skip_store");
        return {falseE, rewrite_status::RW_DONE};
      }
    }
  }

  // normalize neq: a != b ==> !(a=b)
  if (isOpX<NEQ>(exp)) {
    Expr negation = mk<EQ>(lhs, rhs);
    return {mk<NEG>(negation), rewrite_status::RW_2};
  }
  return {exp, rewrite_status::RW_DONE};
}

rewrite_result ITERewriteRule::operator()(Expr exp) {
  seahorn::ScopedStats _st("rw_ite");
  if (!isOpX<ITE>(exp)) {
    return {exp, rewrite_status::RW_SKIP};
  }

  Expr i = exp->arg(0);
  Expr t = exp->arg(1);
  Expr e = exp->arg(2);
  // ite(a, true, false) => a
  if (isOpX<TRUE>(t) && isOpX<FALSE>(e)) {
    return {i, rewrite_status::RW_DONE};
  }
  // ite(a, false, true) => !a
  if (isOpX<FALSE>(t) && isOpX<TRUE>(e)) {
    return {mk<NEG>(i), rewrite_status::RW_1}; // simp dbl negation
  }
  // ite(i, a, a) => a
  if (t == e) {
    return {t, rewrite_status::RW_DONE};
  }
  // ite(a, b, ite(!a, c, d)) => ite(a, b, c)
  if (isOpX<ITE>(e)) {
    Expr e_i = e->arg(0);
    Expr e_t = e->arg(1);
    if (op::boolop::areNegations(i, e_i)) {
      return {mk<ITE>(i, t, e_t), rewrite_status::RW_1};
    }
  }
  // ite(true, a, b) => a
  if (isOpX<TRUE>(i)) {
    return {t, rewrite_status::RW_DONE};
  }
  // ite(false, a, b) => b
  if (isOpX<FALSE>(i)) {
    return {e, rewrite_status::RW_DONE};
  }
  return {exp, rewrite_status::RW_DONE};
}

} // namespace expr
