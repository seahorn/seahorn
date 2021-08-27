#include "seahorn/Expr/ExprRewriter.hh"
#include "seahorn/Expr/ExprVisitor.hh"

namespace expr {

namespace utils {
bool shouldCache(Expr e) { return e->use_count() > 1; }
} // namespace utils

Expr rewriteITEComp(Expr exp) {
  ExprRewriter<ITECompRewriteConfig> rewriter(exp->efac());
  return rewriter.rewriteExpr(exp);
}

bool ITECompRewriteConfig::shouldRewrite(Expr exp) {
  return isOpX<ITE>(exp) || isOpX<CompareOp>(exp);
}

rewrite_result ITECompRewriteConfig::applyRewriteRules(Expr exp) {
  rewrite_result res = {exp, rewrite_status::RW_SKIP};
  if (isOpX<ITE>(exp)) {
    res = m_iteRule(exp);
  } else if (isOpX<CompareOp>(exp)) {
    res = m_compRule(exp);
  }
  return res;
}
} // namespace expr
