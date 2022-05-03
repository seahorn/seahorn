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
/// XXX: belongs in memory specific modules (mem repr)?
/**
 * If arr is one of:
 * 1) store, or
 * 2) ITE,
 * then push select(..., idx) down the expression tree;
 * for nested, we presume the tree is biased towards "then" side (arg[1])
 **/
Expr pushSelectDownStoreITE(Expr arr, Expr idx, AddrRangeMap &arm,
                            DagVisitCache &cache);

// over-approximates whether ptr pointer is in arm; only returns False
// when ptr is well-formed PE and is for sure not in arm
bool inAddrRange(Expr ptr, AddrRangeMap &arm);

bool isMemWriteOp(Expr);
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
  ExprFactory &efac;    // for making expr
  DagVisitCache &cache; // for deep rewrite using rewriter

  Expr trueE;
  Expr falseE;

  ExprRewriteRule(ExprFactory &efac, DagVisitCache &cache)
      : efac(efac), trueE(mk<TRUE>(efac)), falseE(mk<FALSE>(efac)),
        cache(cache) {}
  ExprRewriteRule(const ExprRewriteRule &o)
      : efac(o.efac), trueE(o.trueE), falseE(o.falseE), cache(o.cache) {}

  rewrite_result operator()(Expr exp) { return {exp, rewrite_status::RW_DONE}; }
};

struct ITERewriteRule : public ExprRewriteRule {
  ITERewriteRule(ExprFactory &efac, DagVisitCache &cache)
      : ExprRewriteRule(efac, cache) {}
  ITERewriteRule(const ITERewriteRule &o) : ExprRewriteRule(o) {}

  rewrite_result operator()(Expr exp) {
    if (!isOpX<ITE>(exp)) {
      return {exp, rewrite_status::RW_SKIP};
    }

    Expr i = exp->arg(0);
    Expr t = exp->arg(1);
    Expr e = exp->arg(2);
    // ite(a, true, false) => a
    if (isOpX<TRUE>(t) && isOpX<FALSE>(e)) {
      return {i, rewrite_status::RW_DONE};
    }
    // ite(a, false, true) => !a
    if (isOpX<FALSE>(t) && isOpX<TRUE>(e)) {
      return {mk<NEG>(i), rewrite_status::RW_1}; // simp dbl negation
    }
    // ite(i, false, false) => false
    if (isOpX<FALSE>(t) && isOpX<FALSE>(e)) {
      return {falseE, rewrite_status::RW_DONE};
    }
    // ite(i, true, true) => true
    if (isOpX<TRUE>(t) && isOpX<TRUE>(e)) {
      return {trueE, rewrite_status::RW_DONE};
    }
    // ite(a, b, ite(!a, c, d)) => ite(a, b, c)
    if (isOpX<ITE>(e)) {
      Expr e_i = e->arg(0);
      Expr e_t = e->arg(1);
      if (op::boolop::areNegations(i, e_i)) {
        return {mk<ITE>(i, t, e_t), rewrite_status::RW_1};
      }
    }
    // ite(true, a, b) => a
    if (isOpX<TRUE>(i)) {
      return {t, rewrite_status::RW_DONE};
    }
    // ite(false, a, b) => b
    if (isOpX<FALSE>(i)) {
      return {e, rewrite_status::RW_DONE};
    }
    return {exp, rewrite_status::RW_SKIP};
  }
};

struct CompareRewriteRule : public ExprRewriteRule {

  CompareRewriteRule(ExprFactory &efac, DagVisitCache &cache)
      : ExprRewriteRule(efac, cache) {}
  CompareRewriteRule(const CompareRewriteRule &o) : ExprRewriteRule(o) {}

  rewrite_result operator()(Expr exp) {
    if (!isOpX<CompareOp>(exp)) {
      return {exp, rewrite_status::RW_SKIP};
    }
    Expr lhs = exp->left();
    Expr rhs = exp->right();

    /* a op b comp a op c ==> b comp c
      e.g. (a - b) == (a - c) ==> b == c
    */
    if (isOpX<BvOp>(lhs) && lhs->op() == rhs->op() &&
        lhs->arity() == rhs->arity() && lhs->arity() == 2) {
      if (lhs->arg(0) == rhs->arg(0)) {
        Expr res = efac.mkBin(exp->op(), lhs->arg(1), rhs->arg(1));
        return {res, rewrite_status::RW_1};
      }
      if (lhs->arg(1) == rhs->arg(1)) {
        Expr res = efac.mkBin(exp->op(), lhs->arg(0), rhs->arg(0));
        return {res, rewrite_status::RW_1};
      }
    }
    // a == a => true, only works if a is constant bvnum
    if (isOpX<EQ>(exp)) {
      bool bothNum = op::bv::is_bvnum(lhs) && op::bv::is_bvnum(rhs);
      bool bothAddr = expr::mem::isBaseAddr(lhs) && expr::mem::isBaseAddr(rhs);
      if (bothNum || bothAddr) {
        if (lhs->arg(0) == rhs->arg(0)) {
          return {trueE, rewrite_status::RW_DONE};
        } else {
          return {falseE, rewrite_status::RW_DONE};
        }
      }
    }

    // normalize neq: a != b ==> !(a=b)
    if (isOpX<NEQ>(exp)) {
      Expr negation = mk<EQ>(lhs, rhs);
      return {mk<NEG>(negation), rewrite_status::RW_2};
    }

    // [k comp ite(a, b, c)] => [ite(a, b comp k, c comp k)]
    // if b, c, or k is ITE, we could have size explosion
    if (isOpX<ITE>(lhs)) {
      rewrite_status st = rewrite_status::RW_2;
      if (isOpX<ITE>(rhs) || isOpX<ITE>(lhs->arg(1)) ||
          isOpX<ITE>(lhs->arg(2))) {
        st = rewrite_status::RW_DONE;
      }
      Expr new_i = lhs->arg(0);
      Expr new_t = efac.mkBin(exp->op(), lhs->arg(1), rhs);
      Expr new_e = efac.mkBin(exp->op(), lhs->arg(2), rhs);
      return {mk<ITE>(new_i, new_t, new_e), st};
    } else if (isOpX<ITE>(rhs)) {
      rewrite_status st = rewrite_status::RW_2;
      if (isOpX<ITE>(lhs) || isOpX<ITE>(rhs->arg(1)) ||
          isOpX<ITE>(rhs->arg(2))) {
        st = rewrite_status::RW_DONE;
      }
      Expr new_i = rhs->arg(0);
      Expr new_t = efac.mkBin(exp->op(), rhs->arg(1), lhs);
      Expr new_e = efac.mkBin(exp->op(), rhs->arg(2), lhs);
      return {mk<ITE>(new_i, new_t, new_e), st};
    }
    return {exp, rewrite_status::RW_SKIP};
  }
};

struct BoolOpRewriteRule : public ExprRewriteRule {
  BoolOpRewriteRule(ExprFactory &efac, DagVisitCache &cache)
      : ExprRewriteRule(efac, cache) {}
  BoolOpRewriteRule(const CompareRewriteRule &o) : ExprRewriteRule(o) {}

  rewrite_result operator()(Expr exp) {
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
struct ArrayRewriteRule : public ExprRewriteRule {
  AddrRangeMap &addrRange;
  ArrayRewriteRule(ExprFactory &efac, DagVisitCache &cache, AddrRangeMap &arm)
      : addrRange(arm), ExprRewriteRule(efac, cache) {}
  ArrayRewriteRule(const ArrayRewriteRule &o)
      : addrRange(o.addrRange), ExprRewriteRule(o) {}

  rewrite_result operator()(Expr exp) {
    if (!isOpX<SELECT>(exp)) {
      return {exp, rewrite_status::RW_SKIP};
    }
    Expr arr = exp->arg(0);
    Expr idx = exp->arg(1);
    /** Read-over-write/ite: push select down to leaves
     **/
    if (isOpX<STORE>(arr) || isOpX<ITE>(arr)) {
      seahorn::Stats::resume("hybrid-mem-push");
      Expr res = utils::pushSelectDownStoreITE(arr, idx, addrRange, cache);
      seahorn::Stats::stop("hybrid-mem-push");

      return {res, rewrite_status::RW_1};
    }
    return {exp, rewrite_status::RW_SKIP};
  }
};

struct ArithmeticRule : public ExprRewriteRule {

  bool m_deepIte;
  ArithmeticRule(ExprFactory &efac, DagVisitCache &cache, bool deepIte = false)
      : ExprRewriteRule(efac, cache), m_deepIte(deepIte) {}
  ArithmeticRule(const ArithmeticRule &o) : ExprRewriteRule(o) {}

  rewrite_result operator()(Expr exp) {
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
      args.push_back(op::bv::bvnum(sum, width, efac));
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
