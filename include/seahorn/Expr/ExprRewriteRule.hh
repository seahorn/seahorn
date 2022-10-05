#pragma once
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprAddrRangeMap.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprMemUtils.h"
#include "seahorn/Expr/ExprOpArray.hh"
#include "seahorn/Expr/ExprOpBv.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/ExprOpMem.hh"
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

bool isMemWriteOp(Expr);

inline Expr ptrAdd(Expr a, Expr b) { return mk<BADD>(a, b); }

inline Expr ptrSub(Expr a, Expr b) { return mk<BSUB>(a, b); }

inline Expr ptrUle(Expr a, Expr b) { return mk<BULE>(a, b); }
/** begin <= i <= end **/
inline Expr ptrInRangeCheck(Expr begin, Expr i, Expr end) {
  return mk<AND>(ptrUle(begin, i), ptrUle(i, end));
}

} // end of namespace utils

enum rewrite_status {
  RW_DONE = 0,
  RW_1 = 1,
  RW_2 = 2,
  RW_FULL = 4,
  RW_SKIP = 5
};

struct rewrite_result {
  Expr rewritten;
  rewrite_status status;
};

struct ExprRewriteRule : public std::unary_function<Expr, rewrite_result> {
  ExprFactory &m_efac;    // for making expr
  DagVisitCache &m_cache; // for deep rewrite using rewriter

  Expr trueE;
  Expr falseE;

  ExprRewriteRule(ExprFactory &efac, DagVisitCache &cache)
      : m_efac(efac), trueE(mk<TRUE>(efac)), falseE(mk<FALSE>(efac)),
        m_cache(cache) {}
  ExprRewriteRule(const ExprRewriteRule &o)
      : m_efac(o.m_efac), trueE(o.trueE), falseE(o.falseE), m_cache(o.m_cache) {
  }

  rewrite_result operator()(Expr exp) { return {exp, rewrite_status::RW_DONE}; }
};

struct ITERewriteRule : public ExprRewriteRule {
  ITERewriteRule(ExprFactory &efac, DagVisitCache &cache)
      : ExprRewriteRule(efac, cache) {}
  ITERewriteRule(const ITERewriteRule &o) : ExprRewriteRule(o) {}

  rewrite_result operator()(Expr exp);
};

struct CompareRewriteRule : public ExprRewriteRule {
  unsigned m_ptrWidth;
  PtrTypeCheckCache &m_ptcCache;
  ARMCache &m_armCache;
  CompareRewriteRule(ExprFactory &efac, DagVisitCache &cache,
                     PtrTypeCheckCache &ptcCache, ARMCache &armCache,
                     unsigned ptrWidth)
      : m_ptrWidth(ptrWidth), m_ptcCache(ptcCache), m_armCache(armCache),
        ExprRewriteRule(efac, cache) {}
  CompareRewriteRule(const CompareRewriteRule &o)
      : m_ptrWidth(o.m_ptrWidth), m_ptcCache(o.m_ptcCache),
        m_armCache(o.m_armCache), ExprRewriteRule(o) {}

  rewrite_result operator()(Expr exp);
};

struct BoolOpRewriteRule : public ExprRewriteRule {
  BoolOpRewriteRule(ExprFactory &efac, DagVisitCache &cache)
      : ExprRewriteRule(efac, cache) {}
  BoolOpRewriteRule(const CompareRewriteRule &o) : ExprRewriteRule(o) {}

  rewrite_result operator()(Expr exp) {
    // seahorn::ScopedStats _st("rw_bool");
    if (!isOpX<BoolOp>(exp)) {
      return {exp, rewrite_status::RW_SKIP};
    }

    if (isOpX<NEG>(exp)) {
      Expr neg = exp->arg(0);
      // double neg => truthy
      // e.g. !(!a) ==> a
      if (isOpX<NEG>(neg)) {
        return {neg->arg(0), rewrite_status::RW_DONE};
      }
      // !ite(c, a, b) => ite(c, !a, !b)
      if (isOpX<ITE>(neg)) {
        return {
            mk<ITE>(neg->arg(0), mk<NEG>(neg->arg(1)), mk<NEG>(neg->arg(2))),
            rewrite_status::RW_1};
      }
      // negate trivial constants: !true => false; !false => true
      if (isOpX<TRUE>(neg)) {
        return {falseE, rewrite_status::RW_DONE};
      }
      if (isOpX<FALSE>(neg)) {
        return {trueE, rewrite_status::RW_DONE};
      }
    }
    return {exp, rewrite_status::RW_SKIP};
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
      : m_armCache(armCache), m_ptCache(ptCache), m_smapCache(smapCache),
        ExprRewriteRule(efac, cache), m_wordSize(wordSz), m_ptrWidth(ptrWidth) {
  }
  ReadOverWriteRule(const ReadOverWriteRule &o)
      : m_armCache(o.m_armCache), m_ptCache(o.m_ptCache),
        m_smapCache(o.m_smapCache), ExprRewriteRule(o),
        m_wordSize(o.m_wordSize), m_ptrWidth(o.m_ptrWidth) {}

  rewrite_result operator()(Expr exp);

private:
  rewrite_result rewriteReadOverStore(Expr arr, Expr idx);

  rewrite_result rewriteReadOverIte(Expr arr, Expr idx);

  rewrite_result rewriteReadOverMemset(Expr arr, Expr idx);

  rewrite_result rewriteReadOverMemcpy(Expr arr, Expr idx);

  rewrite_result rewriteReadOverStoreMap(Expr arr, Expr idx);

  /* Given select(storemap(arr, base, smap), idx), revert into ite form
  return true if select(arr) is already rewritten and stored in cache */
  bool revertSMapToIte(Expr storeMap, Expr idx, Expr &res);
};

// for eager pre-processing stores during storeWord
struct WriteOverWriteRule : public ExprRewriteRule {
  unsigned m_ptrWidth;
  op::array::StoreMapCache &m_smapC;
  WriteOverWriteRule(ExprFactory &efac, DagVisitCache &cache,
                     op::array::StoreMapCache &sC, unsigned ptrWidth)
      : m_ptrWidth(ptrWidth), m_smapC(sC), ExprRewriteRule(efac, cache) {}
  WriteOverWriteRule(const WriteOverWriteRule &o)
      : m_ptrWidth(o.m_ptrWidth), m_smapC(o.m_smapC), ExprRewriteRule(o) {}

  rewrite_result operator()(Expr exp);

  rewrite_result rewriteStore(Expr exp);
};

struct ArithmeticRule : public ExprRewriteRule {

  bool m_deepIte;
  ArithmeticRule(ExprFactory &efac, DagVisitCache &cache, bool deepIte = false)
      : ExprRewriteRule(efac, cache), m_deepIte(deepIte) {}
  ArithmeticRule(const ArithmeticRule &o) : ExprRewriteRule(o) {}

  rewrite_result operator()(Expr exp) {
    // seahorn::ScopedStats _st("rw_arith");
    if (!isOpX<BADD>(exp)) {
      return {exp, rewrite_status::RW_SKIP};
    }
    if (m_deepIte) {
      /**
      pushing add down ite is expensive(exponential), so only use with shallow
      expressions;
      bvadd(ite(i, a, b), c) ==> ite(i, bvadd(a, c), bvadd(b, c))
      bvadd(c, ite(i, a, b)) ==> ite(i, bvadd(a, c), bvadd(b, c))
      **/
      Expr lhs = exp->left();
      Expr rhs = exp->right();
      if (isOpX<ITE>(lhs)) {
        Expr i = lhs->first();
        Expr addL = mk<BADD>(lhs->arg(1), rhs);
        Expr addR = mk<BADD>(lhs->arg(2), rhs);
        return {mk<ITE>(i, addL, addR), rewrite_status::RW_2};
      } else if (isOpX<ITE>(rhs)) {
        Expr i = rhs->first();
        Expr addL = mk<BADD>(rhs->arg(1), lhs);
        Expr addR = mk<BADD>(rhs->arg(2), lhs);
        return {mk<ITE>(i, addL, addR), rewrite_status::RW_2};
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
    return {res, rewrite_status::RW_DONE};
  }
};

} // namespace expr
