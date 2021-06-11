#pragma once
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/ExprVisitor.hh"

#include "seahorn/Expr/Expr.hh"

namespace expr {

namespace op {
namespace boolop {

/** lhs == a and rhs == !a
 *  or:
 *  lhs == !a and rhs == a
 **/
bool areNegations(Expr lhs, Expr rhs);

struct ITESimplifier : public std::unary_function<Expr, Expr> {
  ExprFactory &efac;

  Expr trueE;
  Expr falseE;

  ITESimplifier(ExprFactory &efac)
      : efac(efac), trueE(mk<TRUE>(efac)), falseE(mk<FALSE>(efac)) {}
  ITESimplifier(const ITESimplifier &o)
      : efac(o.efac), trueE(o.trueE), falseE(o.falseE) {}

  Expr operator()(Expr exp) {
    // skip if not ITE or CompOp
    if (!isOpX<ITE>(exp) && !isOp<CompareOp>(exp)) {
      return exp;
    }

    if (isOpX<ITE>(exp)) {
      Expr i = exp->arg(0);
      Expr t = exp->arg(1);
      Expr e = exp->arg(2);
      // ite(a, true, false) => a
      if (t == trueE && e == falseE) {
        return i;
      }
      // ite(a, b, ite(!a, c, d)) => ite(a, b, c)
      if (isOpX<ITE>(e)) {
        Expr e_i = e->arg(0);
        Expr e_t = e->arg(1);
        if (areNegations(i, e_i)) {
          return boolop::lite(i, t, e_t);
        }
      }
    }

    if (isOp<CompareOp>(exp)) {
      Expr lhs = exp->left();
      Expr rhs = exp->right();
      // [k comp ite(a, b, c)] => [ite(a, b comp k, c comp k)]
      if (isOpX<ITE>(lhs)) {
        Expr new_i = lhs->arg(0);
        Expr new_t = efac.mkBin(exp->op(), lhs->arg(1), rhs);
        Expr new_e = efac.mkBin(exp->op(), lhs->arg(2), rhs);
        return lite(new_i, new_t, new_e);
      } else if (isOpX<ITE>(rhs)) {
        Expr new_i = rhs->arg(0);
        Expr new_t = efac.mkBin(exp->op(), rhs->arg(1), lhs);
        Expr new_e = efac.mkBin(exp->op(), rhs->arg(2), lhs);
        return lite(new_i, new_t, new_e);
      }
    }
    return exp;
  }
};

/** trivial simplifier for Boolean and Compare Operators */
struct TrivialSimplifier : public std::unary_function<Expr, Expr> {
  ExprFactory &efac;

  Expr trueE;
  Expr falseE;

  TrivialSimplifier(const TrivialSimplifier &o)
      : efac(o.efac), trueE(o.trueE), falseE(o.falseE) {}

  TrivialSimplifier(ExprFactory &fac)
      : efac(fac), trueE(mk<TRUE>(efac)), falseE(mk<FALSE>(efac)) {}

  Expr operator()(Expr exp) {
    if (exp == trueE || exp == falseE)
      return exp;

    if (!isOp<BoolOp>(exp))
      return exp;

    if (isOpX<IMPL>(exp)) {
      // TRUE -> x  == x
      if (trueE == exp->left())
        return exp->right();

      // FALSE -> x == TRUE
      if (falseE == exp->left())
        return trueE;

      // x -> TRUE == TRUE
      if (trueE == exp->right())
        return trueE;

      // x -> FALSE == !x
      if (falseE == exp->right())
        return lneg(exp->left());

      return exp;
    }

    if (isOpX<IFF>(exp)) {
      if (exp->left() == exp->right())
        return exp->left();
      if (trueE == exp->left())
        return exp->right();
      if (falseE == exp->left())
        return lneg(exp->right());
      if (trueE == exp->right())
        return exp->left();
      if (falseE == exp->right())
        return lneg(exp->left());

      return exp;
    }

    if (isOpX<NEG>(exp)) {
      // -- !TRUE -> FALSE
      if (trueE == exp->left())
        return falseE;
      // -- !FALSE -> TRUE
      if (falseE == exp->left())
        return trueE;
      // -- ! ! x -> x
      if (isOpX<NEG>(exp->left()))
        return exp->left()->left();
      return exp;
    }

    int arity = exp->arity();
    if (isOpX<OR>(exp)) {
      if (arity == 0)
        return falseE;
      if (arity == 1)
        return exp->left();
      if (arity == 2) {
        ENode *lhs = exp->left();
        ENode *rhs = exp->right();

        if (lhs == rhs)
          return lhs;
        if (trueE == lhs || trueE == rhs)
          return trueE;
        if (falseE == lhs)
          return rhs;
        if (falseE == rhs)
          return lhs;
        // (!a || a) or (a || !a)
        if (areNegations(lhs, rhs)) {
          return trueE;
        }

        return exp;
      }

      // -- arity > 2, check if one arguments is true
      for (ENode *arg : mk_it_range(exp->args_begin(), exp->args_end()))
        if (trueE == arg)
          return trueE;
      return exp;
    }

    if (isOpX<AND>(exp)) {
      if (arity == 0)
        return trueE;
      if (arity == 1)
        return exp->left();

      if (exp->arity() == 2) {
        ENode *lhs = exp->left();
        ENode *rhs = exp->right();

        if (lhs == rhs)
          return lhs;
        if (falseE == lhs || falseE == rhs)
          return falseE;
        if (trueE == lhs)
          return rhs;
        if (trueE == rhs)
          return lhs;
        // (!a && a) or (a && !a)
        if (areNegations(lhs, rhs)) {
          return falseE;
        }

        return exp;
      }

      // -- arity > 2, check if one arguments  is false
      for (ENode *arg : mk_it_range(exp->args_begin(), exp->args_end()))
        if (falseE == arg)
          return falseE;
      return exp;
    }

    return exp;
  }
};
} // namespace boolop
} // namespace op

namespace {

template <typename M>
struct RVSIMP : public std::unary_function<Expr, VisitAction> {
  typedef typename M::const_iterator const_iterator;

  const M &map;

  std::shared_ptr<boolop::TrivialSimplifier> r;

  typedef RVSIMP<M> this_type;

  RVSIMP(const this_type &o) : map(o.map), r(o.r) {}
  RVSIMP(ExprFactory &fac, const M &m)
      : map(m), r(std::make_shared<boolop::TrivialSimplifier>(fac)) {}

  VisitAction operator()(Expr exp) const {
    const_iterator it = map.find(exp);

    if (it == map.end())
      return VisitAction::changeDoKidsRewrite(exp, r);

    return VisitAction::changeTo(it->second);
  }
};

} // namespace

/** Replace and simplify */
template <typename M> Expr replaceSimplify(Expr exp, const M &map) {
  RVSIMP<M> rv(exp->efac(), map);
  return dagVisit(rv, exp);
}

namespace op {
namespace boolop {
template <typename T> struct BS {
  std::shared_ptr<T> _r;

  BS(std::shared_ptr<T> r) : _r(r) {}
  BS(T *r) : _r(r) {}

  VisitAction operator()(Expr exp) {
    // -- apply the rewriter
    if (isOp<BoolOp>(exp))
      return VisitAction::changeDoKidsRewrite(exp, _r);

    // -- do not descend into non-boolean operators
    return VisitAction::skipKids();
  }
};

// simplifying visitor for boolop and compareop
template <typename T> struct BoolCompSV {
  std::shared_ptr<T> _r;

  BoolCompSV(std::shared_ptr<T> r) : _r(r) {}
  BoolCompSV(T *r) : _r(r) {}

  VisitAction operator()(Expr exp) {
    // -- apply the rewriter
    if (isOp<BoolOp>(exp) || isOp<CompareOp>(exp))
      return VisitAction::changeDoKidsRewrite(exp, _r);

    // -- do not descend into non-boolean, non-compare operators
    return VisitAction::skipKids();
  }
};

} // namespace boolop
} // namespace op
} // namespace expr
