#include "seahorn/Expr/ExprRewriter.hh"
#include "seahorn/Expr/ExprVisitor.hh"
#include "seahorn/Support/Stats.hh"
#include "llvm/Support/CommandLine.h"

namespace seahorn {
extern bool BasedPtrObj; // from BvOpSem2RawMemMgr.cc
} // namespace seahorn
static llvm::cl::opt<bool>
    UseArm("horn-hybrid-use-arm",
           llvm::cl::desc("Use ARM abstraction to simplify mem expr"),
           llvm::cl::init(false));
namespace expr {
using namespace addrRangeMap;
namespace utils {
bool shouldCache(Expr e) {
  if (isOpX<SELECT>(e)) {
    return op::array::selectArray(e)->use_count() > 1;
  }
  return e->use_count() > 1;
}

bool inAddrRange(Expr ptr, AddrRangeMap &arm) {
  if (!BasedPtrObj)
    return true;
  if (expr::mem::isBaseAddr(ptr)) {
    return arm.count(ptr) > 0;
  }
  if ((isOpX<BADD>(ptr) /*|| isOpX<BSUB>(ptr)*/) && ptr->arity() == 2) {
    Expr lhs = ptr->arg(0);
    Expr rhs = ptr->arg(1);
    Expr base, offset;
    if (expr::mem::isBaseAddr(lhs)) {
      base = lhs;
      offset = rhs;
    } else if (expr::mem::isBaseAddr(rhs)) {
      base = rhs;
      offset = lhs;
    } else
      return true; // over-approx
    if (!op::bv::is_bvnum(offset))
      return true; // offset is symbolic, over-approx
    mpz_class offsetMpz = op::bv::toMpz(offset);
    auto offsetNum = offsetMpz.get_ui();
    return arm.contains(base, offsetNum);
  }
  return true; // over-approx
}

bool isMemWriteOp(Expr e) {
  return isOpX<STORE>(e) || isOpX<ITE>(e) || isOpX<MEMSET_WORDS>(e) ||
         isOpX<MEMCPY_WORDS>(e);
}
} // namespace utils

bool ITECompRewriteConfig::shouldRewrite(Expr exp) {
  return isOpX<ITE>(exp) || isOpX<CompareOp>(exp) || isOpX<BoolOp>(exp) ||
         isOpX<SELECT>(exp) || isOpX<BADD>(exp);
}

rewrite_result ITECompRewriteConfig::applyRewriteRules(Expr exp) {
  rewrite_result res = {exp, rewrite_status::RW_SKIP};
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

bool PointerArithmeticConfig::shouldRewrite(Expr exp) {
  return isOpX<BADD>(exp) || isOpX<ITE>(exp);
}

rewrite_result PointerArithmeticConfig::applyRewriteRules(Expr exp) {
  rewrite_result res = {exp, rewrite_status::RW_SKIP};
  if (isOpX<BADD>(exp)) {
    res = m_arithRule(exp);
  }
  return res;
}

rewrite_result ArrayRewriteRule::operator()(Expr exp) {
  if (!isOpX<SELECT>(exp)) {
    return {exp, rewrite_status::RW_SKIP};
  }
  Expr arr = exp->arg(0);
  Expr idx = exp->arg(1);
  /** Read-over-write/ite: push select down to leaves
   **/
  if (isOpX<STORE>(arr)) {
    Expr arrN = op::array::storeArray(arr);
    Expr idxN = op::array::storeIdx(arr);
    if (UseArm) {
      if (!approxPtrEq(idx, idxN, m_armCache,
                       m_ptCache)) { /* idx!=idxN must be true*/
        seahorn::Stats::count("hybrid.arm_skip_store");
        return {op::array::select(arrN, idx), rewrite_status::RW_1};
      }
    }
    Expr res = mk<ITE>(mk<EQ>(idx, idxN), op::array::storeVal(arr),
                       op::array::select(arrN, idx));
    return {res, rewrite_status::RW_2};
  } else if (isOpX<ITE>(arr)) {
    Expr i = arr->arg(0);
    Expr t = arr->arg(1);
    Expr e = arr->arg(2);
    Expr res = mk<ITE>(i, op::array::select(t, idx), op::array::select(e, idx));
    return {res, rewrite_status::RW_2};
  } else if (isOpX<MEMSET_WORDS>(arr)) {
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
  } else if (isOpX<MEMCPY_WORDS>(arr)) {
    /** select(copy(a, p, b, q, s), i) =>
     * ITE(p ≤ i < p + s, read(b, q + (i − p)), read(a, i)) **/
    Expr res;
    Expr dstMem = arr->arg(0);
    Expr srcMem = arr->arg(1);
    Expr dstIdx = arr->arg(2);
    Expr srcIdx = arr->arg(3);
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
  } else {
    return {exp, rewrite_status::RW_DONE};
  }
}

} // namespace expr
