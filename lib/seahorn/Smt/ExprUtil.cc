/// All Expr utilitiies.
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprNumericUtils.hh"
#include "seahorn/Expr/ExprSimplifier.hh"
#include "seahorn/Expr/ExprVisitor.hh"
/// yet to be refactored

namespace expr {

namespace {
struct CIRCSIZE : public std::unary_function<Expr, VisitAction> {
  unsigned ands;
  unsigned ors;
  unsigned inputs;

  CIRCSIZE() : ands(0), ors(0), inputs(0) {}

  VisitAction operator()(Expr e) {
    if (isOpX<AND>(e))
      ands++;
    else if (isOpX<OR>(e))
      ors++;
    else if (!isOpX<NEG>(e)) {
      inputs++;
      return VisitAction::skipKids();
    }
    return VisitAction::doKids();
  }

  unsigned size() { return ands + ors + inputs; }
};
} // namespace

namespace op {
namespace boolop {
/// size of an expression in terms of ANDs, ORs, and inputs.
/// NEG is not counted, other BoolOps are treated as inputs.
unsigned circSize(Expr e) {
  CIRCSIZE csz;
  dagVisit(csz, e);
  return csz.size();
}

unsigned circSize(const ExprVector &vec) {
  CIRCSIZE csz;
  dagVisit(csz, vec);
  return csz.size();
}
} // namespace boolop
} // namespace op

namespace {
struct SIZE : public std::unary_function<Expr, VisitAction> {
  size_t count;

  SIZE() : count(0) {}

  VisitAction operator()(Expr exp) {
    count++;
    return VisitAction::doKids();
  }
};
} // namespace

/** Size of an expression as a DAG */
size_t dagSize(Expr e) {
  SIZE sz;
  dagVisit(sz, e);
  return sz.count;
}

size_t dagSize(const ExprVector &vec) {
  SIZE sz;
  dagVisit(sz, vec);
  return sz.count;
}

/** Size of an expression as a tree */
size_t treeSize(Expr e) {
  SIZE sz;
  visit(sz, e);
  return sz.count;
}

namespace {
struct CV : public std::unary_function<Expr, VisitAction> {
  Expr e;
  bool found;
  ExprSet seen;

  CV(const CV &o) : e(o.e), found(o.found), seen(o.seen) {
    llvm_unreachable(nullptr);
  }

  CV(Expr exp) : e(exp), found(false) {}

  VisitAction operator()(Expr exp) {
    if (found || seen.count(exp) > 0 || e == exp) {
      found = true;
      return VisitAction::skipKids();
    }
    seen.insert(e);
    return VisitAction::doKids();
  }
};
} // namespace

/** Returns true if e1 contains e2 as a sub-expression */
bool contains(Expr e1, Expr e2) {
  CV cv(e2);
  dagVisit(cv, e1);
  return cv.found;
}

namespace {
struct RAV : public std::unary_function<Expr, VisitAction> {
  Expr s;
  Expr t;

  RAV(const RAV &o) : s(o.s), t(o.t) {}
  RAV(Expr _s, Expr _t) : s(_s), t(_t) {}
  VisitAction operator()(Expr exp) const {
    return exp == s ? VisitAction::changeTo(t) : VisitAction::doKids();
  }
};
} // namespace
// -- replace all occurrences of s by t
Expr replaceAll(Expr exp, Expr s, Expr t) {
  RAV rav(s, t);
  return dagVisit(rav, exp);
}

namespace {
struct RAVSIMP : public std::unary_function<Expr, VisitAction> {
  Expr s;
  Expr t;

  std::shared_ptr<boolop::TrivialSimplifier> r;

  RAVSIMP(const RAVSIMP &o) : s(o.s), t(o.t), r(o.r) {}
  RAVSIMP(Expr _s, Expr _t)
      : s(_s), t(_t),
        r(std::make_shared<boolop::TrivialSimplifier>(s->efac())) {}

  VisitAction operator()(Expr exp) const {
    if (exp == s)
      return VisitAction::changeTo(t);
    return VisitAction::changeDoKidsRewrite(exp, r);
  }
};
} // namespace

/** Replace all occurrences of s by t while simplifying the result */
Expr replaceAllSimplify(Expr exp, Expr s, Expr t) {
  RAVSIMP rav(s, t);
  return dagVisit(rav, exp);
}

namespace op {
namespace boolop {
/**
 * Very simple simplifier for Boolean Operators
 */
Expr simplify(Expr exp) {
  BS<TrivialSimplifier> bs(std::make_shared<TrivialSimplifier>(exp->efac()));
  return dagVisit(bs, exp);
}

namespace {
/** Rewriter that normalizes AND/OR operators */
struct NormalizeOps : public std::unary_function<Expr, Expr> {
  Expr trueE;
  Expr falseE;

  NormalizeOps() : trueE(0), falseE(0) {}

  NormalizeOps(const NormalizeOps &o) : trueE(o.trueE), falseE(o.falseE) {}

  Expr operator()(Expr exp) {
    // -- create true/false constants for convinience
    if (trueE == nullptr) {
      trueE = mk<TRUE>(exp->efac());
      falseE = mk<FALSE>(exp->efac());
    }

    // -- skip anything that is not AND/OR
    if (!(isOpX<AND>(exp) || isOpX<OR>(exp)))
      return exp;
    if (exp->arity() == 1)
      return exp->left();

    const Operator &op = exp->op();
    Expr top, bot;
    if (isOpX<AND>(exp)) {
      top = trueE;
      bot = falseE;
    } else {
      top = falseE;
      bot = trueE;
    }

    if (exp->arity() == 0)
      return top;

    if (exp->arity() == 2) {
      if (isOpX<AND>(exp))
        return land(exp->left(), exp->right());
      else /* isOpX<OR> */
        return lor(exp->left(), exp->right());
    }

    ExprSet newArgs;
    for (Expr a : mk_it_range(exp->args_begin(), exp->args_end()))
      if (!(op == a->op())) {
        if (a == bot)
          return bot;
        else if (a != top)
          newArgs.insert(a);
      } else /* descend into kids that have the same top-level operator */
        for (Expr ka : mk_it_range(a->args_begin(), a->args_end()))
          if (ka == bot)
            return bot;
          else if (ka != top)
            newArgs.insert(ka);

    if (newArgs.empty())
      return top;
    if (newArgs.size() == 1)
      return *(newArgs.begin());

    boost::container::flat_set<Expr> args(newArgs.begin(), newArgs.end());
    Expr res = top;
    for (Expr arg : llvm::reverse(args))
      res = isOpX<AND>(exp) ? land(arg, res) : lor(arg, res);

    return res;
  }

  Expr land(Expr f, Expr g) {
    /** base cases */
    if (f == trueE)
      return g;
    if (g == trueE)
      return f;
    if (f == falseE || g == falseE)
      return falseE;
    if (f == g)
      return f;
    if (f == boolop::lneg(g) || boolop::lneg(f) == g)
      return falseE;

    // -- both not AND operators. Order in some way
    if (!isOpX<AND>(f) && !isOpX<AND>(g))
      return g < f ? mk<AND>(f, g) : mk<AND>(g, f);

    Expr topf = isOpX<AND>(f) ? f->left() : f;
    Expr topg = isOpX<AND>(g) ? g->left() : g;

    Expr top, restF, restG;
    if (topf < topg || topf == topg) {
      top = topf;
      restF = isOpX<AND>(f) ? f->right() : trueE;
    } else
      restF = f;

    if (topg < topf || topg == topf) {
      top = topg;
      restG = isOpX<AND>(g) ? g->right() : trueE;
    } else
      restG = g;

    return boolop::land(top, land(restF, restG));
  }

  Expr lor(Expr f, Expr g) {
    /** base cases */
    if (f == falseE)
      return g;
    if (g == falseE)
      return f;
    if (f == trueE || g == trueE)
      return trueE;
    if (f == g)
      return f;
    if (f == boolop::lneg(g) || boolop::lneg(f) == g)
      return trueE;

    // -- both not AND operators. Order in some way
    if (!isOpX<OR>(f) && !isOpX<OR>(g))
      return g < f ? mk<OR>(f, g) : mk<OR>(g, f);

    Expr topf = isOpX<OR>(f) ? f->left() : f;
    Expr topg = isOpX<OR>(g) ? g->left() : g;

    Expr top, restF, restG;
    if (topf < topg || topf == topg) {
      top = topf;
      restF = isOpX<OR>(f) ? f->right() : falseE;
    } else
      restF = f;

    if (topg < topf || topg == topf) {
      top = topg;
      restG = isOpX<OR>(g) ? g->right() : falseE;
    } else
      restG = g;

    return boolop::lor(top, lor(restF, restG));
  }
};
}
/**
 * Very simple normalizer for AND/OR expressions
 */
Expr norm(Expr exp) {
  BS<NormalizeOps> bs(new NormalizeOps());
  return dagVisit(bs, exp);
}

namespace {
/** Rewriter that gathers Boolean operators into n-ary ones */
struct GatherOps : public std::unary_function<Expr, Expr> {
  Expr trueE;
  Expr falseE;

  GatherOps() : trueE(0), falseE(0) {}

  GatherOps(const GatherOps &o) : trueE(o.trueE), falseE(o.falseE) {}

  Expr operator()(Expr exp) {
    // -- create true/false constants for convinience
    if (trueE == nullptr) {
      trueE = mk<TRUE>(exp->efac());
      falseE = mk<FALSE>(exp->efac());
    }

    // -- skip terminals
    if (exp->arity() == 0)
      return exp;
    // if (!isBoolOp<X> (exp)) return exp;
    // -- skip anything that is not AND/OR
    if (!(isOpX<AND>(exp) || isOpX<OR>(exp)))
      return exp;

    const Operator &op = exp->op();
    Expr top;
    Expr bot;
    if (isOpX<AND>(exp)) {
      top = trueE;
      bot = falseE;
    } else {
      top = falseE;
      bot = trueE;
    }

    ExprSet newArgs;
    for (Expr a : mk_it_range(exp->args_begin(), exp->args_end()))
      if (!(op == a->op())) {
        if (a == bot)
          return bot;
        else if (a != top)
          newArgs.insert(a);
      } else /* descend into kids that have the same top-level operator */
        for (Expr ka : mk_it_range(a->args_begin(), a->args_end()))
          if (ka == bot)
            return bot;
          else if (ka != top)
            newArgs.insert(ka);

    if (newArgs.empty())
      return top;
    if (newArgs.size() == 1)
      return *(newArgs.begin());
    return exp->efac().mkNary(op, newArgs.begin(), newArgs.end());
  }
};
}

/** Gather binary Boolean operators into n-ary ones. Helps
    readability. Best done after NNF */
Expr gather(Expr exp) {
  BS<GatherOps> go(new GatherOps());
  return dagVisit(go, exp);
}

namespace {
/** puts an expression into NNF */
struct NNF : public std::unary_function<Expr, VisitAction> {
  ExprFactory &efac;
  std::shared_ptr<TrivialSimplifier> r;

  NNF(const NNF &o) : efac(o.efac), r(o.r) {}

  NNF(ExprFactory &fac)
      : efac(fac), r(std::make_shared<TrivialSimplifier>(efac)) {}

  VisitAction operator()(Expr exp) {
    if (exp->arity() == 0)
      return VisitAction::skipKids();

    // -- AND / OR -- run the simplifier
    if (isOpX<AND>(exp) || isOpX<OR>(exp))
      return VisitAction::changeDoKidsRewrite(exp, r);

    // -- not a negation, then do not touch, must be non-Boolean
    if (!isOpX<NEG>(exp))
      return VisitAction::skipKids();

    // -- if here, top operator is negation, push it in
    Expr lhs = exp->left();
    if (lhs == r->falseE)
      return VisitAction::changeTo(r->trueE);
    if (lhs == r->trueE)
      return VisitAction::changeTo(r->falseE);

    // -- !!x -- Trivial simplifer will get rid of unary AND
    if (isOpX<NEG>(lhs))
      return VisitAction::changeDoKidsRewrite(mk<AND>(lhs->left()), r);

    // -- ! (x & b) ==> !x || !b
    if (isOpX<OR>(lhs) || isOpX<AND>(lhs)) {
      // -- negate arguments
      ExprVector args;
      for (Expr arg : mk_it_range(lhs->args_begin(), lhs->args_end()))
        args.push_back(lneg(arg));

      // -- flip operator
      Expr res = isOpX<OR>(lhs) ? mknary<AND>(args.begin(), args.end())
                                : mknary<OR>(args.begin(), args.end());
      return VisitAction::changeDoKidsRewrite(res, r);
    }

    // -- negation of anything else, don't descend
    return VisitAction::skipKids();
  }
};

}
/**
 * Converts to NNF. Assumes the only Boolean operators of exp
 * are AND/OR/NEG.
 */
Expr nnf(Expr exp) {
  NNF n(exp->efac());
  return dagVisit(n, exp);
}

/** Makes an expression pretty for printing */
Expr pp(Expr exp) { return gather(nnf(exp)); }
} // namespace boolop
} // namespace op
namespace numeric {

bool getNum(Expr exp, mpz_class &num) {
  if (isOp<MPZ>(exp)) {
    num = getTerm<mpz_class>(exp);

    return true;
  } else if (isOp<UINT>(exp)) {
    unsigned unsignedNum = getTerm<unsigned>(exp);
    num = mpz_class(unsignedNum);

    return true;
  } else if (bv::is_bvnum(exp)) {
    num = bv::toMpz(exp);

    return true;
  }

  return false;
}

bool isNumeric(Expr exp) {
  return isOp<MPZ>(exp) || isOp<UINT>(exp) || bv::is_bvnum(exp);
}

Expr convertToMpz(Expr exp) {
  mpz_class num = 0;
  if (getNum(exp, num)) {
    return mkTerm<mpz_class>(num, exp->efac());
  }

  return exp;
}
} // namespace numeric
} // namespace expr
