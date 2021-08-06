#pragma once
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/ExprSimplifier.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Expr/Smt/Z3.hh"

/* Simplifying rewrite rules for different Exprewrite_status */

namespace expr {

enum rewrite_status { RW_DONE = 0, RW_1 = 1, RW_2 = 2, RW_FULL = 4 };
struct rewrite_result {
  Expr rewritten;
  rewrite_status status;
};

struct ExprRewriteRule : public std::unary_function<Expr, rewrite_result> {
  ExprFactory &efac; // for making expr

  Expr trueE;
  Expr falseE;

  seahorn::EZ3 &m_zctx; // for z3 simplifier if needed

  ExprRewriteRule(ExprFactory &efac, seahorn::EZ3 &zctx)
      : efac(efac), trueE(mk<TRUE>(efac)), falseE(mk<FALSE>(efac)),
        m_zctx(zctx) {}
  ExprRewriteRule(const ExprRewriteRule &o)
      : efac(o.efac), trueE(o.trueE), falseE(o.falseE), m_zctx(o.m_zctx) {}

  rewrite_result operator()(Expr exp) { return {exp, rewrite_status::RW_DONE}; }
};

struct ITERewriteRule : public ExprRewriteRule {
  ITERewriteRule(ExprFactory &efac, seahorn::EZ3 &zctx)
      : ExprRewriteRule(efac, zctx) {}
  ITERewriteRule(const ITERewriteRule &o) : ExprRewriteRule(o) {}

  rewrite_result operator()(Expr exp) {
    if (!isOpX<ITE>(exp)) {
      return {exp, rewrite_status::RW_DONE};
    }

    Expr i = exp->arg(0);
    Expr t = exp->arg(1);
    Expr e = exp->arg(2);
    // ite(a, true, false) => a
    if (t == trueE && e == falseE) {
      return {i, rewrite_status::RW_DONE};
    }
    // ite(a, false, true) => !a
    if (t == falseE && e == trueE) {
      return {mk<NEG>(i), rewrite_status::RW_2}; // simp dbl negation
    }
    // ite(a, b, ite(!a, c, d)) => ite(a, b, c)
    if (isOpX<ITE>(e)) {
      Expr e_i = e->arg(0);
      Expr e_t = e->arg(1);
      if (op::boolop::areNegations(i, e_i)) {
        return {mk<ITE>(i, t, e_t), rewrite_status::RW_DONE};
      }
    }
    return {exp, rewrite_status::RW_DONE};
  }
};

struct CompareRewriteRule : public ExprRewriteRule {
  CompareRewriteRule(ExprFactory &efac, seahorn::EZ3 &zctx)
      : ExprRewriteRule(efac, zctx) {}
  CompareRewriteRule(const CompareRewriteRule &o) : ExprRewriteRule(o) {}

  rewrite_result operator()(Expr exp) {
    if (!isOpX<CompareOp>(exp)) {
      return {exp, rewrite_status::RW_DONE};
    }
    Expr lhs = exp->left();
    Expr rhs = exp->right();
    if (lhs->arity() <= 2 && rhs->arity() <= 2) {
      // use z3 for smaller compare expressions
      Expr simped = z3_simplify(m_zctx, exp);
      return {simped, rewrite_status::RW_DONE};
    }
    // [k comp ite(a, b, c)] => [ite(a, b comp k, c comp k)]
    if (isOpX<ITE>(lhs)) {
      Expr new_i = lhs->arg(0);
      Expr new_t = efac.mkBin(exp->op(), lhs->arg(1), rhs);
      Expr new_e = efac.mkBin(exp->op(), lhs->arg(2), rhs);
      return {mk<ITE>(new_i, new_t, new_e), rewrite_status::RW_2};
    } else if (isOpX<ITE>(rhs)) {
      Expr new_i = rhs->arg(0);
      Expr new_t = efac.mkBin(exp->op(), rhs->arg(1), lhs);
      Expr new_e = efac.mkBin(exp->op(), rhs->arg(2), lhs);
      return {mk<ITE>(new_i, new_t, new_e), rewrite_status::RW_2};
    }
    return {exp, rewrite_status::RW_DONE};
  }
};

} // namespace expr
