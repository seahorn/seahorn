#include "seahorn/Expr/ExprRewriter.hh"
#include "seahorn/Expr/ExprVisitor.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include <unordered_map>

namespace expr {

Expr rewriteITEComp(Expr exp) {
  seahorn::EZ3 zctx(exp->efac());
  ExprRewriter<ITECompRewriteConfig> rewriter(exp->efac(), zctx);
  return rewriter.rewriteExpr(exp);
}

bool ITECompRewriteConfig::shouldRewrite(Expr exp) {
  return isOpX<ITE>(exp) || isOpX<CompareOp>(exp);
}

rewrite_result ITECompRewriteConfig::applyRewriteRules(Expr exp) {
  if (isOpX<ITE>(exp)) {
    return m_iteRule(exp);
  } else if (isOpX<CompareOp>(exp)) {
    return m_compRule(exp);
  } else {
    return {exp, rewrite_status::RW_DONE};
  }
}
} // namespace expr
