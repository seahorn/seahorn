#pragma once
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprAddrRangeMap.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprMemUtils.h"
#include "seahorn/Expr/ExprOpArray.hh"
#include "seahorn/Expr/ExprOpBv.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/ExprOpMem.hh"
#include "seahorn/Expr/ExprRewriter.hh"
#include "seahorn/Expr/ExprSimplifier.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Expr/Smt/Z3.hh"
#include "seahorn/Support/Stats.hh"
#include <algorithm>

/* Simplifying rewrite rules for different Exprewrite_status */
namespace expr {
using namespace mem;
using namespace addrRangeMap; /* addrRangeMap */

namespace utils {

inline Expr ptrAdd(const Expr &a, const Expr &b) { return mk<BADD>(a, b); }
inline Expr ptrSub(const Expr &a, const Expr &b) { return mk<BSUB>(a, b); }
inline Expr ptrUle(const Expr &a, const Expr &b) { return mk<BULE>(a, b); }
/** begin <= i <= end **/
inline Expr ptrInRangeCheck(const Expr &begin, const Expr &i, const Expr &end) {
  return mk<AND>(ptrUle(begin, i), ptrUle(i, end));
}

} // end of namespace utils

struct ExprRewriteRule : public std::unary_function<Expr, RewriteResult> {
  ExprFactory &m_efac;    // for making expr
  DagVisitCache &m_cache; // for deep rewrite using rewriter

  Expr trueE;
  Expr falseE;

  ExprRewriteRule(ExprFactory &efac, DagVisitCache &cache)
      : m_efac(efac), m_cache(cache), trueE(mk<TRUE>(efac)),
        falseE(mk<FALSE>(efac)) {}
  ExprRewriteRule(const ExprRewriteRule &o) = default;

  RewriteResult operator()(const Expr &exp) const { return {exp, RWStatus::RW_DONE}; }
};

struct ITERewriteRule : public ExprRewriteRule {
  ITERewriteRule(ExprFactory &efac, DagVisitCache &cache)
      : ExprRewriteRule(efac, cache) {}
  ITERewriteRule(const ITERewriteRule &o) : ExprRewriteRule(o) {}

  RewriteResult operator()(const Expr &exp) const;
};

struct CompareRewriteRule : public ExprRewriteRule {
  unsigned m_ptrWidth;
  PtrTypeCheckCache &m_ptcCache;
  ARMCache &m_armCache;
  CompareRewriteRule(ExprFactory &efac, DagVisitCache &cache,
                     PtrTypeCheckCache &ptcCache, ARMCache &armCache,
                     unsigned ptrWidth)
      : ExprRewriteRule(efac, cache), m_ptrWidth(ptrWidth),
        m_ptcCache(ptcCache), m_armCache(armCache) {}
  CompareRewriteRule(const CompareRewriteRule &o) = default;

  RewriteResult operator()(const Expr &exp) const;
};

struct BoolOpRewriteRule : public ExprRewriteRule {
  BoolOpRewriteRule(ExprFactory &efac, DagVisitCache &cache)
      : ExprRewriteRule(efac, cache) {}
  BoolOpRewriteRule(const CompareRewriteRule &o) : ExprRewriteRule(o) {}

  RewriteResult operator()(const Expr &exp) const {
    // seahorn::ScopedStats _st("rw_bool");
    if (!isOpX<BoolOp>(exp)) {
      return {exp, RWStatus::RW_SKIP};
    }

    if (isOpX<NEG>(exp)) {
      Expr arg0 = exp->arg(0);
      // double neg => truthy
      // e.g. !(!a) ==> a
      if (isOpX<NEG>(arg0)) {
        return {arg0->arg(0), RWStatus::RW_DONE};
      }
      // !ite(c, a, b) => ite(c, !a, !b)
      if (isOpX<ITE>(arg0)) {
        return {
            mk<ITE>(arg0->arg(0), mk<NEG>(arg0->arg(1)), mk<NEG>(arg0->arg(2))),
            RWStatus::RW_1};
      }
      // negate trivial constants: !true => false; !false => true
      if (isOpX<TRUE>(arg0)) {
        return {falseE, RWStatus::RW_DONE};
      }
      if (isOpX<FALSE>(arg0)) {
        return {trueE, RWStatus::RW_DONE};
      }
    }
    return {exp, RWStatus::RW_SKIP};
  }
};

// for select
struct ReadOverWriteRule : public ExprRewriteRule {
  ARMCache &m_armCache;
  PtrTypeCheckCache &m_ptCache;
  op::array::StoreMapCache &m_smapCache;
  unsigned m_wordSize; // in bytes
  unsigned m_ptrWidth; // ptr size in bits
  ReadOverWriteRule(ExprFactory &efac, DagVisitCache &cache, ARMCache &armCache,
                    expr::PtrTypeCheckCache &ptCache,
                    op::array::StoreMapCache &smapCache, unsigned wordSz,
                    unsigned ptrWidth)
      : ExprRewriteRule(efac, cache), m_armCache(armCache), m_ptCache(ptCache),
        m_smapCache(smapCache), m_wordSize(wordSz), m_ptrWidth(ptrWidth) {}

  ReadOverWriteRule(const ReadOverWriteRule &o) = default;

  RewriteResult operator()(const Expr &exp) const;

private:
  RewriteResult rewriteReadOverStore(const Expr &arr, const Expr &idx) const;

  RewriteResult rewriteReadOverIte(const Expr &arr, const Expr &idx) const;

  RewriteResult rewriteReadOverMemset(const Expr &arr, const Expr &idx) const;

  RewriteResult rewriteReadOverMemcpy(const Expr &arr, const Expr &idx) const;

  RewriteResult rewriteReadOverStoreMap(const Expr &arr, const Expr &idx) const;

  /* Given select(storemap(arr, base, smap), idx), revert into ite form */
  Expr revertSMapToIte(const Expr &storeMap, const Expr &idx) const;
};

// for eager pre-processing stores during storeWord
struct WriteOverWriteRule : public ExprRewriteRule {
  unsigned m_ptrWidth;
  op::array::StoreMapCache &m_smapC;
  WriteOverWriteRule(ExprFactory &efac, DagVisitCache &cache,
                     op::array::StoreMapCache &sC, unsigned ptrWidth)
      : ExprRewriteRule(efac, cache), m_ptrWidth(ptrWidth), m_smapC(sC) {}
  WriteOverWriteRule(const WriteOverWriteRule &o) = default;

  RewriteResult operator()(const Expr &exp) const;
  RewriteResult rewriteStore(const Expr &exp) const;
};

struct ArithmeticRule : public ExprRewriteRule {

  bool m_deepIte;
  ArithmeticRule(ExprFactory &efac, DagVisitCache &cache, bool deepIte = false)
      : ExprRewriteRule(efac, cache), m_deepIte(deepIte) {}
  ArithmeticRule(const ArithmeticRule &o) : ExprRewriteRule(o) {}

  RewriteResult operator()(const Expr &exp) const {
    // seahorn::ScopedStats _st("rw_arith");
    if (!isOpX<BADD>(exp)) {
      return {exp, RWStatus::RW_SKIP};
    }
    if (m_deepIte) {
      /**
      pushing add down ite is expensive(exponential), so only use with shallow
      expressions;
      bvadd(ite(i, a, b), c) ==> ite(i, bvadd(a, c), bvadd(b, c))
      bvadd(c, ite(i, a, b)) ==> ite(i, bvadd(a, c), bvadd(b, c))
      **/
      auto lhs = exp->left();
      auto rhs = exp->right();
      if (isOpX<ITE>(lhs)) {
        auto i = lhs->first();
        Expr addL = mk<BADD>(lhs->arg(1), rhs);
        Expr addR = mk<BADD>(lhs->arg(2), rhs);
        return {mk<ITE>(i, addL, addR), RWStatus::RW_2};
      } else if (isOpX<ITE>(rhs)) {
        Expr i = rhs->first();
        Expr addL = mk<BADD>(rhs->arg(1), lhs);
        Expr addR = mk<BADD>(rhs->arg(2), lhs);
        return {mk<ITE>(i, addL, addR), RWStatus::RW_2};
      }
    }
    /** In general these two rules:
     * 1) flatten n-ary bvadd:
     * bvadd(a, bvadd(b, c), d...) => bvadd(a, b, c, d);
     * 2) consolidate all bvnum operands into one:
     * bvadd(a, 1, 2, d) => bvadd(a, d, 3)
     * **/
    llvm::SmallVector<Expr, 2> args;
    mpz_class sum = 0;
    unsigned width = 0;
    for (auto b = exp->args_begin(), e = exp->args_end(); b != e; ++b) {
      Expr arg = *b;
      if (op::bv::is_bvnum(arg)) {
        mpz_class argNum = op::bv::toMpz(arg);
        sum = argNum + sum;
        width = std::max(op::bv::widthBvNum(arg), width);
      } else if (isOpX<BADD>(arg)) {
        for (auto bKid = arg->args_begin(); bKid != arg->args_end(); ++bKid) {
          Expr kid = *bKid;
          if (op::bv::is_bvnum(kid)) {
            mpz_class kidNum = op::bv::toMpz(kid);
            sum = kidNum + sum;
            width = std::max(op::bv::widthBvNum(kid), width);
          } else {
            /** children has already been flattened **/
            args.push_back(kid);
          }
        }
      } else {
        args.push_back(arg);
      }
    }
    // bv num always at the back
    if (width > 0) {
      args.push_back(op::bv::bvnum(sum, width, m_efac));
    }
    Expr res;
    if (args.size() > 1) {
      res = mknary<BADD>(args.begin(), args.end());
    } else
      res = *args.begin();
    return {res, RWStatus::RW_DONE};
  }
};

} // namespace expr
