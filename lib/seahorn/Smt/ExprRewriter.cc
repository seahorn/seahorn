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
} // namespace utils

Expr rewriteHybridLoadExpr(Expr loadE, AddrRangeMap &arm, unsigned wordSize,
                           unsigned ptrWidth) {
  DagVisitCache newCache;
  return rewriteMemExprWithCache<ITECompRewriteConfig>(loadE, arm, newCache,
                                                       wordSize, ptrWidth);
}

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
} // namespace expr
