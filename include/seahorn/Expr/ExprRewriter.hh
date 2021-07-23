#pragma once
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprRewriteRule.hh"

namespace expr {
using namespace seahorn;

Expr rewriteITEComp(Expr exp);

struct RewriteFrame {
  Expr exp;
  size_t depth;
  RewriteFrame(Expr exp, size_t depth) : exp(exp), depth(depth) {}
};

using ExprVisitedMap = std::unordered_map<ENode *, bool>;
using RewriteFrameVector = std::vector<RewriteFrame>;

class ExprRewriterConfig {
  /* apply rewrite rules */
protected:
  ExprFactory &m_efac; // for making expr
  EZ3 &m_zctx; // for z3 simplifier if needed

public:
  ExprRewriterConfig(ExprFactory &efac, EZ3 &zctx)
      : m_efac(efac), m_zctx(zctx) {}

  rewrite_result applyRewriteRules(Expr exp);

  bool shouldRewrite(Expr exp);
};

/* example config for ITE */
class ITECompRewriteConfig : public ExprRewriterConfig {
private:
  ITERewriteRule m_iteRule;
  CompareRewriteRule m_compRule;
public:
  ITECompRewriteConfig(ExprFactory &efac, EZ3 &zctx)
      : m_iteRule(efac, zctx), m_compRule(efac, zctx),
        ExprRewriterConfig(efac, zctx) {}

  rewrite_result applyRewriteRules(Expr exp);

  bool shouldRewrite(Expr exp);
};

template <typename Config>
class ExprRewriter {
protected:
  Config m_config;
  ExprFactory &m_efac;  // for making expr
  EZ3 &m_zctx; // for z3 simplifier if needed

  // Expr m_exp; // input Expr
  RewriteFrameVector m_frameStack;
  DagVisitCache m_cache;
  ExprVisitedMap m_visited;

  /* starting for root, build worklist wl; depth is limited by *maxDepth* */
  void buildVisitWorklist(Expr root, size_t maxDepth) {
    // need to store visited info
    RewriteFrameVector preStack = {RewriteFrame(root, maxDepth)};
    bool limitedDepth = (maxDepth != rewrite_status::RW_FULL);

    while (!preStack.empty()) {
      RewriteFrame cur = preStack.back();
      preStack.pop_back();
      Expr curE = cur.exp;
      size_t curDepth = cur.depth;
      if (limitedDepth && curDepth <= 0) {
        continue;
      }
      if (m_visited.find(&*curE) != m_visited.end()) {
        continue;
      }
      if (!m_config.shouldRewrite(curE)) {
        continue;
      }
      m_visited[&*curE] = true;
      m_frameStack.push_back(cur);
      for (auto b = curE->args_begin(), e = curE->args_end(); b != e; b++) {
        Expr child = *b;
        size_t childDepth = limitedDepth ? curDepth - 1 : curDepth;
        preStack.push_back(RewriteFrame(child, childDepth));
      }
    }
  }

public:
  ExprRewriter(ExprFactory &efac, EZ3 &zctx)
      : m_efac(efac), m_zctx(zctx), m_config(efac, zctx) {}

  Expr processExpr(Expr exp) {
    buildVisitWorklist(exp, rewrite_status::RW_FULL);
    Expr res;
    while (!m_frameStack.empty()) {
      RewriteFrame top = m_frameStack.back();
      m_frameStack.pop_back();

      res = top.exp;
      if (findInDagVisitCache(m_cache, top.exp) != top.exp) {
        continue;
      }
      if (res->arity() > 0) {
        ExprVector kids;
        bool changed = false;
        for (auto b = top.exp->args_begin(); b != top.exp->args_end(); ++b) {
          // children already rewritten, get from cache
          Expr k = findInDagVisitCache(m_cache, *b);
          kids.push_back(k);
          changed = (changed || k.get() != *b);
        }
        if (changed) {
          if (!res->isMutable())
            res = res->getFactory().mkNary(res->op(), kids.begin(), kids.end());
          else
            res->renew_args(kids.begin(), kids.end());
        }
      }
      rewrite_result rwRes = m_config.applyRewriteRules(res);
      rewrite_status st = rwRes.status;
      res = rwRes.rewritten;
      m_cache[&*top.exp] = res;
      if (st != rewrite_status::RW_DONE) {
        buildVisitWorklist(res, st);
      }
    }
    return res;
  }
};

} // end of namespace expr
