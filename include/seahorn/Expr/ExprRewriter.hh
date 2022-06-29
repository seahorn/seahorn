#pragma once
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprRewriteRule.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

namespace expr {
using namespace seahorn;
using namespace mem;

namespace utils {
bool shouldCache(Expr e);
} // end of namespace utils

/** rewrite hybrid memory expr in ITE structure
 * loadMem: Expr tree that represents value loaded from current memory state
 * ptr: address Expr tree
 **/
// Expr rewriteHybridLoadExpr(Expr loadE, AddrRangeMap &arm);

struct RewriteFrame {
  Expr m_exp;       // the Expr node (subtree) under rewrite
  size_t m_depth;   // number of levels to rewrite from this node
  size_t m_i;       // up to m_i th children have been rewritten
  bool m_rewriting; // this frame is currently under further rewrite
  RewriteFrame(Expr exp, size_t depth, size_t i, bool rw = false)
      : m_exp(exp), m_depth(depth), m_i(i), m_rewriting(rw) {}
};

using RewriteFrameVector = std::vector<RewriteFrame>;

class ExprRewriterConfig {
  /* apply rewrite rules */
protected:
  ExprFactory &m_efac;    // for making expr
  DagVisitCache &m_cache; // for accessing cached rewrite results

public:
  ExprRewriterConfig(ExprFactory &efac, DagVisitCache &cache)
      : m_efac(efac), m_cache(cache) {}

  rewrite_result applyRewriteRules(Expr exp);

  bool shouldRewrite(Expr exp);
};

/* example config for ITE */
class ITECompRewriteConfig : public ExprRewriterConfig {
private:
  ITERewriteRule m_iteRule;      // Fig 1
  CompareRewriteRule m_compRule; // Fig 3
  BoolOpRewriteRule m_boolRule;  // Fig 4
  ArrayRewriteRule m_arrayRule;  // Fig 2
  ArithmeticRule m_arithRule;    // Fig 5

public:
  ITECompRewriteConfig(ExprFactory &efac, DagVisitCache &cache, ARMCache &armC,
                       PtrTypeCheckCache &ptCache, unsigned wordSize,
                       unsigned ptrWidth)
      : m_iteRule(efac, cache), m_compRule(efac, cache),
        m_boolRule(efac, cache),
        m_arrayRule(efac, cache, armC, ptCache, wordSize, ptrWidth),
        m_arithRule(efac, cache), ExprRewriterConfig(efac, cache) {}

  rewrite_result applyRewriteRules(Expr exp);

  bool shouldRewrite(Expr exp);
};

/* config for normalising pointer bvadd */
class PointerArithmeticConfig : public ExprRewriterConfig {
private:
  ArithmeticRule m_arithRule;

public:
  PointerArithmeticConfig(ExprFactory &efac, DagVisitCache &cache)
      : m_arithRule(efac, cache, true), ExprRewriterConfig(efac, cache) {}

  rewrite_result applyRewriteRules(Expr exp);

  bool shouldRewrite(Expr exp);
};

template <typename Config> class ExprRewriter {
protected:
  Config &m_config;
  ExprFactory &m_efac; // for making expr

  RewriteFrameVector m_rewriteStack;
  ExprVector m_resultStack;
  DagVisitCache &m_cache;

  /* visit e, return true if any of the following is true:
    1. e has been cached, or
    2. current depth is 0 or
    3. current m_config is dictates e should not be further visited
    in any of the above case, push e to top of result stack
    otherwise return false and push e into top of rewriteStack
  */
  bool visit(Expr e, size_t depth) {
    if (depth == 0 || !m_config.shouldRewrite(e)) {
      m_resultStack.push_back(e);
      return true;
    }
    if (utils::shouldCache(e)) {
      DagVisitCache::const_iterator cit = m_cache.find(&*e);
      if (cit != m_cache.end()) {
        m_resultStack.push_back(cit->second);
        return true;
      }
    }
    size_t nextDepth = (depth == rewrite_status::RW_FULL) ? depth : depth - 1;
    m_rewriteStack.push_back(RewriteFrame(e, nextDepth, 0));
    return false;
  }

  void addToCache(Expr src, Expr rw) {
    if (utils::shouldCache(src)) {
      src->Ref();
      m_cache[&*src] = rw;
    }
  }

public:
  ExprRewriter(ExprFactory &efac, Config &config, DagVisitCache &cache)
      : m_efac(efac), m_config(config), m_cache(cache) {}

  void processFrame(RewriteFrame &frame) {
    Expr exp = frame.m_exp;
    size_t arity = exp->arity();
    while (frame.m_i < arity) {
      Expr kid = exp->arg(frame.m_i);
      frame.m_i++;
      if (!visit(kid, frame.m_depth))
        return;
    }
    m_rewriteStack.pop_back();
    // all kids of exp has been visited, collect rewritten kids to form
    // new expression
    bool changed = false;
    SmallVector<Expr, 4> new_kids;
    size_t end = m_resultStack.size();
    size_t begin = end - arity;
    for (size_t i = begin, j = 0; i < end; i++, j++) {
      new_kids.push_back(m_resultStack[i]);
      changed = changed || (m_resultStack[i] != exp->arg(j));
    }
    Expr new_exp = changed ? exp->getFactory().mkNary(
                                 exp->op(), new_kids.begin(), new_kids.end())
                           : exp;
    m_resultStack.resize(begin);
    // apply rewrite rules to expression with new kids
    rewrite_result rwRes = m_config.applyRewriteRules(new_exp);
    if (rwRes.status == rewrite_status::RW_SKIP) {
      m_resultStack.push_back(rwRes.rewritten);
      /* cache multi-step */
      if (!m_rewriteStack.empty() && m_rewriteStack.back().m_rewriting) {
        auto &original = m_rewriteStack.back();
        Expr key = original.m_exp;
        m_rewriteStack.pop_back();
        addToCache(key, rwRes.rewritten);
      }
    } else if (rwRes.status == rewrite_status::RW_DONE) {
      Expr key = exp;
      /* cache multi-step */
      if (!m_rewriteStack.empty() && m_rewriteStack.back().m_rewriting) {
        auto &original = m_rewriteStack.back();
        key = original.m_exp;
        m_rewriteStack.pop_back();
      }
      addToCache(key, rwRes.rewritten);
      m_resultStack.push_back(rwRes.rewritten);
    } else {
      /* current frame is the base of a multi-step rewrite, keep in rw stack */
      if (m_rewriteStack.empty() || !m_rewriteStack.back().m_rewriting) {
        frame.m_rewriting = true;
        m_rewriteStack.push_back(frame);
      }
      m_rewriteStack.push_back(RewriteFrame(rwRes.rewritten, rwRes.status, 0));
    }
  }

  Expr rewriteExpr(Expr root) {
    if (visit(root, rewrite_status::RW_FULL)) {
      return m_resultStack.back();
    }
    while (!m_rewriteStack.empty()) {
      processFrame(m_rewriteStack.back());
    }
    return m_resultStack.back();
  }
};
} // end of namespace expr
