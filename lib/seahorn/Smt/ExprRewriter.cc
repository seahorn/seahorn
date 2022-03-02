#include "seahorn/Expr/ExprRewriter.hh"
#include "seahorn/Expr/ExprVisitor.hh"

namespace seahorn {
extern bool BasedPtrObj; // from BvOpSem2RawMemMgr.cc
}

namespace expr {
using namespace addrRangeMap;
namespace utils {
bool shouldCache(Expr e) { return e->use_count() > 1; }

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
    // return arm.count(base) > 0;
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

Expr pushSelectDownStoreITE(Expr arr, Expr idx, AddrRangeMap &arm,
                            DagVisitCache &cache) {
  if (!isMemWriteOp(arr)) {
    return op::array::select(arr, idx);
  }
  Expr res;          // final rewritten ITE
  ExprVector nested; // nested store/ITEs being selected from
  Expr child = arr;
  while (isMemWriteOp(child)) {
    nested.push_back(child);
    // store/memset/memcpy all use 1st argument
    size_t childIdx = isOpX<ITE>(child) ? 1 : 0;
    child = child->arg(childIdx);
  }
  // construct ITE from btm up
  Expr back = nested.back();
  while (!nested.empty()) {
    back = nested.back();
    if (isOpX<STORE>(back)) {
      /** node case: store(rewritten, idxN, valN) =>
       * ite(idx == idxN, valN, rewritten) **/
      Expr arrN = back->arg(0);
      Expr idxN = op::array::storeIdx(back);
      if (!utils::inAddrRange(idxN, arm)) { /* idx != idxN must be true */
        LOG("opsem.hybrid", WARN << *idxN << " is not in range \n");
        res = op::array::select(arrN, idx);
        nested.pop_back();
        continue;
      }
      Expr valN = op::array::storeVal(back);
      if (isOpX<SELECT>(valN)) { // XXX: remove selects here
        expr::addrRangeMap::ARMCache c;
        Expr branchIdx = op::array::selectIdx(valN);
        AddrRangeMap branchArm =
            expr::addrRangeMap::addrRangeMapOf(branchIdx, c);
        valN = pushSelectDownStoreITE(op::array::selectArray(valN), branchIdx,
                                      branchArm, cache);
      }
      Expr compE = mk<EQ>(idx, idxN);
      Expr simpCompE =
          rewriteMemExprWithCache<ITECompRewriteConfig>(compE, arm, cache);
      if (!res)
        res = op::array::select(arrN, idx);
      if (isOpX<TRUE>(simpCompE)) {
        res = valN;
      } else if (isOpX<FALSE>(simpCompE)) {
        /* res = res */
      } else {
        res = mk<ITE>(simpCompE, valN, res);
      }
    } else if (isOpX<ITE>(back)) {
      /** must be ITE.
       * node case: ite(iN, rewritten, eN) =>
       * ite(iN, rewritten, select(eN, idx))
       **/
      Expr iN = back->arg(0);
      Expr tN = back->arg(1);
      Expr simpIN =
          rewriteMemExprWithCache<ITECompRewriteConfig>(iN, arm, cache);
      Expr eN = back->arg(2);
      Expr newE;
      if (isMemWriteOp(eN)) {
        newE = pushSelectDownStoreITE(eN, idx, arm, cache);
      } else {
        newE = op::array::select(eN, idx);
      }
      if (!res) {
        res = op::array::select(tN, idx);
      }
      if (isOpX<TRUE>(simpIN)) {
        /* res = res */
      } else if (isOpX<FALSE>(simpIN)) {
        res = newE;
      } else {
        res = mk<ITE>(simpIN, res, newE);
      }
    }
    nested.pop_back();
  }
  return res;
}
} // namespace utils

Expr rewriteHybridLoadExpr(Expr loadE, AddrRangeMap &arm) {
  DagVisitCache newCache;
  return rewriteMemExprWithCache<ITECompRewriteConfig>(loadE, arm, newCache);
}

bool ITECompRewriteConfig::shouldRewrite(Expr exp) {
  return isOpX<ITE>(exp) || isOpX<CompareOp>(exp) || isOpX<BoolOp>(exp) ||
         isOpX<SELECT>(exp) || isOpX<STORE>(exp) || isOpX<BADD>(exp);
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
} // namespace expr
