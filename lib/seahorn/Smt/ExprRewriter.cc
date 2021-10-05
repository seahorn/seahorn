#include "seahorn/Expr/ExprRewriter.hh"
#include "seahorn/Expr/ExprVisitor.hh"

namespace expr {

namespace utils {
bool shouldCache(Expr e) { return e->use_count() > 1; }

Expr pushSelectDownStoreITE(Expr arr, Expr idx, DagVisitCache &cache) {
  if (!isOpX<STORE>(arr) && !isOpX<ITE>(arr)) {
    return op::array::select(arr, idx);
  }
  Expr res;          // final rewritten ITE
  ExprVector nested; // nested store/ITEs being selected from
  Expr child = arr;
  while (isOpX<STORE>(child) || isOpX<ITE>(child)) {
    nested.push_back(child);
    size_t childIdx = isOpX<STORE>(child) ? 0 : 1;
    child = child->arg(childIdx);
  }

  Expr back = nested.back();
  if (isOpX<STORE>(back)) {
    /** leaf case for *back* is store(arrn, idxn, valn):
     * ite(idx == idxn, valn, select(arrn, idx))
     **/
    Expr arrN = back->arg(0);
    Expr idxN = back->arg(1);
    Expr valN = back->arg(2);
    Expr compE = mk<EQ>(idx, idxN);
    Expr simpCompE = rewriteExprWithCache<ITECompRewriteConfig>(compE, cache);
    if (isOpX<TRUE>(simpCompE)) {
      res = valN;
    } else if (isOpX<FALSE>(simpCompE)) {
      res = op::array::select(arrN, idx);
    } else {
      res = mk<ITE>(simpCompE, valN, op::array::select(arrN, idx));
    }
  } else {
    /** must be ITE.
     * leaf case for *back* is ite(iN, tN, eN):
     * ite(iN, select(tN, idx), select(eN, idx))
     **/
    Expr iN = back->arg(0);
    Expr tN = back->arg(1);
    Expr eN = back->arg(2);
    Expr newE;
    if (isOpX<STORE>(eN) || isOpX<ITE>(eN)) {
      newE = pushSelectDownStoreITE(eN, idx, cache);
    } else {
      newE = op::array::select(eN, idx);
    }
    Expr simpIN = rewriteExprWithCache<ITECompRewriteConfig>(iN, cache);
    if (isOpX<TRUE>(simpIN)) {
      res = op::array::select(tN, idx);
    } else if (isOpX<FALSE>(simpIN)) {
      res = newE;
    } else {
      res = mk<ITE>(iN, op::array::select(tN, idx), newE);
    }
  }
  nested.pop_back();
  // construct ITE from btm up
  while (!nested.empty()) {
    back = nested.back();
    if (isOpX<STORE>(back)) {
      /** node case: store(rewritten, idxN, valN) =>
       * ite(idx == idxN, valN, rewritten) **/
      Expr compE = mk<EQ>(idx, back->arg(1));
      Expr simpCompE = rewriteExprWithCache<ITECompRewriteConfig>(compE, cache);
      if (isOpX<TRUE>(simpCompE)) {
        res = back->arg(2);
      } else if (isOpX<FALSE>(simpCompE)) {
        /* res = res */
      } else {
        res = mk<ITE>(simpCompE, back->arg(2), res);
      }
    } else {
      /** must be ITE.
       * node case: ite(iN, rewritten, eN) =>
       * ite(iN, rewritten, select(eN, idx))
       **/
      Expr iN = back->arg(0);
      Expr simpIN = rewriteExprWithCache<ITECompRewriteConfig>(iN, cache);
      Expr eN = back->arg(2);
      Expr newE;
      if (isOpX<STORE>(eN) || isOpX<ITE>(eN)) {
        newE = pushSelectDownStoreITE(eN, idx, cache);
      } else {
        newE = op::array::select(eN, idx);
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

Expr rewriteITEComp(Expr exp) {
  DagVisitCache newCache;
  return rewriteExprWithCache<ITECompRewriteConfig>(exp, newCache);
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
} // namespace expr
