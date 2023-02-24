#pragma once
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprRewriteRule.hh"
#include "seahorn/Expr/ExprRewriter.hh"

namespace expr {

using namespace seahorn;
using namespace mem;

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
  bool shouldRewrite(const Expr &exp) const;
  bool shouldCache(const Expr &e) const {
    return ExprRewriterConfigBase::shouldCache(e) || utils::shouldCache(e);
  }
};

/* config for normalising pointer bvadd */
class PointerArithmeticConfig : public ExprRewriterConfigBase {
private:
  ArithmeticRule m_arithRule;

public:
  PointerArithmeticConfig(ExprFactory &efac, DagVisitCache &cache)
      : ExprRewriterConfigBase(efac, cache), m_arithRule(efac, cache, true) {}

  RewriteResult doRewrite(const Expr &exp);
  bool shouldRewrite(const Expr &exp) const;

  bool shouldCache(const Expr &e) const {
    return ExprRewriterConfigBase::shouldCache(e) || utils::shouldCache(e);
  }
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

  bool shouldCache(const Expr &e) const {
    return ExprRewriterConfigBase::shouldCache(e) || utils::shouldCache(e);
  }

  void onAfterRewrite(const Expr &oldE, const Expr &newE) const;
};

} // namespace expr
