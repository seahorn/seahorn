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
bool shouldCache(const Expr &e);
} // end of namespace utils

struct RewriteFrame {
  // the Expr node (subtree) under rewrite
  Expr m_exp;

  // number of levels to rewrite from this node
  unsigned m_depth:4;
  // up to m_i th children have been rewritten
  unsigned m_i:16;
  // this frame is currently under further rewrite
  unsigned m_rewriting:1;

  RewriteFrame(Expr exp, RWStatus depth, size_t i, bool rw = false)
      : m_exp(exp), m_depth(depth), m_i(i), m_rewriting(rw) {}
};

using RewriteFrameVector = std::vector<RewriteFrame>;

/// \brief Base class for rewrite configuration
class ExprRewriterConfigBase {
  /* apply rewrite rules */
protected:
  ExprFactory &m_efac;
  // for accessing cached rewrite results
  DagVisitCache &m_cache;

public:
  ExprRewriterConfigBase(ExprFactory &efac, DagVisitCache &cache)
      : m_efac(efac), m_cache(cache) {}

  bool shouldCache(const Expr &e) { return e->use_count() > 1; }

  // RewriteResult doRewrite(Expr exp);

  // bool shouldRewrite(Expr exp);

  // /* Given original Expr oldE and rewritten newE, do actions like
  //   update cache, logging, etc */
  // void onAfterRewrite(Expr oldE, Expr newE);
};

/// \brief A generic bottom up expression rewriter
///
/// Rewrite rules are embedded in \p Config template argument
template <typename Config> class ExprRewriter {
protected:
  Config &m_config;
  ExprFactory &m_efac; // for making expr

  RewriteFrameVector m_rewriteStack;
  ExprVector m_resultStack;
  DagVisitCache &m_cache;

  /*** \brief visits an expression

       returns true if expression has been rewritten, and false if ti is placed
       back on the rewrite stack

    visit \p e, return true if any of the following is true:
    1. e has been cached, or
    2. current depth is 0 or
    3. current \p m_config  dictates that \p e should not be further visited
    in any of the above cases, push \p e to top of \p m_resultStack
    otherwise return false and push \p e into top of \p m_rewriteStack
  */
  bool visit(const Expr &e, size_t depth) {
    // -- no need to rewrite
    if (depth == 0 || !m_config.shouldRewrite(e)) {
      m_resultStack.push_back(e);
      return true;
    }

    // -- lookup in cache
    if (m_config.shouldCache(e)) {
      auto cit = m_cache.find(&*e);
      if (cit != m_cache.end()) {
        m_resultStack.push_back(cit->second);
        return true;
      }
    }

    // -- place new item on rewrite stack
    unsigned nextDepth = (depth == RWStatus::RW_FULL) ? depth : depth - 1;
    m_rewriteStack.emplace_back(e, RWStatus(nextDepth), 0);
    return false;
  }

  /// \brief adds the pair (src, rw) to the cache
  bool addToCache(const Expr &src, const Expr &rw) {
    if (m_config.shouldCache(src)) {
      assert(src != rw);
      src->Ref();
      m_cache.insert({&*src, rw});
      return true;
    }
    return false;
  }

  /// \brief Returns true if the rewrite is nested in a rewrite
  bool isInNestedRewrite() const {
    return !m_rewriteStack.empty() && m_rewriteStack.back().m_rewriting;
  }

public:
  ExprRewriter(ExprFactory &efac, Config &config, DagVisitCache &cache)
      : m_config(config), m_efac(efac), m_cache(cache) {}

  void processTopFrame() {
    RewriteFrame &frame = m_rewriteStack.back();
    // seahorn::Stats::resume("rewriter.try-visit");
    const Expr &exp = frame.m_exp;
    size_t arity = exp->arity();

    while (frame.m_i < arity) {
      const Expr &kid = exp->arg(frame.m_i++);
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
      const Expr &kid = m_resultStack[i];
      new_kids.push_back(kid);
      changed = changed || (kid != exp->arg(j));
    }

    Expr newExp = changed ? exp->getFactory().mkNary(
                                exp->op(), new_kids.begin(), new_kids.end())
                          : exp;
    m_resultStack.resize(begin);

    // apply rewrite rules to expression with new kids
    RewriteResult rwRes = m_config.doRewrite(newExp);
    m_config.onAfterRewrite(exp, rwRes.exp);

    switch (rwRes.status) {
    case RWStatus::RW_SKIP:
      m_resultStack.push_back(rwRes.exp);

      // cache nested rewrite
      if (isInNestedRewrite()) {
        addToCache(m_rewriteStack.back().m_exp, rwRes.exp);
        m_rewriteStack.pop_back();
      }

      break;
    case RWStatus::RW_DONE:
      m_resultStack.push_back(rwRes.exp);

      // cache nested rewrite
      if (isInNestedRewrite()) {
        addToCache(m_rewriteStack.back().m_exp, rwRes.exp);
        m_rewriteStack.pop_back();
      } else {
        // normal caching
        addToCache(exp, rwRes.exp);
      }

      assert(exp == m_rewriteStack.back().m_exp);

      break;
    default:
      /* current frame is the base of a multi-step rewrite, keep in rw stack */
      if (!isInNestedRewrite()) {
        frame.m_rewriting = true;
        m_rewriteStack.push_back(frame);
      }
      m_rewriteStack.emplace_back(rwRes.exp, rwRes.status, 0);
    }
  }

  Expr rewriteExpr(Expr root) {
    if (visit(root, RWStatus::RW_FULL)) {
      return m_resultStack.back();
    }
    while (!m_rewriteStack.empty()) {
      processTopFrame();
    }
    return m_resultStack.back();
  }
};

/************************************************************************/
/* Specific rewriters */
/************************************************************************/

/* example config for ITE */
class ITECompRewriteConfig : public ExprRewriterConfigBase {
private:
  ITERewriteRule m_iteRule;      // Fig 1
  CompareRewriteRule m_compRule; // Fig 3
  BoolOpRewriteRule m_boolRule;  // Fig 4
  ReadOverWriteRule m_arrayRule; // Fig 2
  ArithmeticRule m_arithRule;    // Fig 5

public:
  ITECompRewriteConfig(ExprFactory &efac, DagVisitCache &cache, ARMCache &armC,
                       PtrTypeCheckCache &ptC, op::array::StoreMapCache &smC,
                       unsigned wordSize, unsigned ptrWidth)
      : ExprRewriterConfigBase(efac, cache), m_iteRule(efac, cache),
        m_compRule(efac, cache, ptC, armC, ptrWidth), m_boolRule(efac, cache),
        m_arrayRule(efac, cache, armC, ptC, smC, wordSize, ptrWidth),
        m_arithRule(efac, cache) {}

  RewriteResult doRewrite(const Expr &exp);
  bool shouldRewrite(const Expr &exp);
  bool shouldCache(const Expr &e) {
    if (ExprRewriterConfigBase::shouldCache(e))
      return true;
    return utils::shouldCache(e);
  }
  void onAfterRewrite(Expr oldE, Expr newE) {}
};

/* config for normalising pointer bvadd */
class PointerArithmeticConfig : public ExprRewriterConfigBase {
private:
  ArithmeticRule m_arithRule;

public:
  PointerArithmeticConfig(ExprFactory &efac, DagVisitCache &cache)
      : ExprRewriterConfigBase(efac, cache), m_arithRule(efac, cache, true) {}

  RewriteResult doRewrite(const Expr &exp);
  bool shouldRewrite(const Expr &exp);

  bool shouldCache(const Expr &e) {
    if (ExprRewriterConfigBase::shouldCache(e))
      return true;
    return utils::shouldCache(e);
  }

  void onAfterRewrite(const Expr &oldE, const Expr &newE) {}
};

/* config for eager-rewriting store */
class WriteOverWriteConfig : public ExprRewriterConfigBase {
private:
  ArithmeticRule m_arithRule;
  WriteOverWriteRule m_wowRule;

public:
  WriteOverWriteConfig(ExprFactory &efac, DagVisitCache &cache,
                       op::array::StoreMapCache &sC, unsigned ptrWidth)
      : ExprRewriterConfigBase(efac, cache), m_arithRule(efac, cache, true),
        m_wowRule(efac, cache, sC, ptrWidth) {}

  RewriteResult doRewrite(const Expr &exp);

  bool shouldRewrite(const Expr &exp);

  bool shouldCache(const Expr &e) {
    if (ExprRewriterConfigBase::shouldCache(e))
      return true;
    return utils::shouldCache(e);
  }

  void onAfterRewrite(Expr const &oldE, const Expr &newE);
};

} // end of namespace expr
