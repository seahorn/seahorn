#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprSimplifier.hh"

namespace seahorn {
namespace path_bmc {

using namespace expr;

// Remove all boolean operators except AND/OR/NEG
struct PreNNF : public std::unary_function<Expr, Expr> {
  PreNNF() {}

  Expr operator()(Expr exp) {

    if (!isOp<BoolOp>(exp)) {
      return exp;
    }

    if (!isOpX<IMPL>(exp) && !isOpX<ITE>(exp) && !isOpX<IFF>(exp) &&
        !isOpX<XOR>(exp)) {
      return exp;
    }

    if (isOpX<XOR>(exp)) {
      assert(false && "TODO");
      return exp;
    } else if (isOpX<IMPL>(exp)) {
      return op::boolop::lor(op::boolop::lneg(exp->left()), exp->right());
    } else if (isOpX<ITE>(exp)) {
      assert(exp->arity() == 3);
      Expr c = exp->operator[](0);
      Expr e1 = exp->operator[](1);
      Expr e2 = exp->operator[](2);
      return op::boolop::lor(op::boolop::land(c, e1),
                             op::boolop::land(op::boolop::lneg(c), e2));
    } else {
      assert(isOpX<IFF>(exp));
      return op::boolop::land(
          op::boolop::lor(op::boolop::lneg(exp->left()), exp->right()),
          op::boolop::lor(op::boolop::lneg(exp->right()), exp->left()));
    }
  }
};

// Perform boolean abstraction
struct BA : public std::unary_function<Expr, VisitAction> {

  bool is_pos_bool_lit(Expr e) const {
    return (isOpX<TRUE>(e) || isOpX<FALSE>(e) || bind::isBoolConst(e));
  }

  bool is_neg_bool_lit(Expr e) const {
    return (isOpX<NEG>(e) && is_pos_bool_lit(e->left()));
  }

  bool is_bool_lit(Expr e) const {
    return (is_pos_bool_lit(e) || is_neg_bool_lit(e));
  }

  ExprFactory &efac;
  std::shared_ptr<op::boolop::TrivialSimplifier> r;

  BA(const BA &o) : efac(o.efac), r(o.r) {}

  BA(ExprFactory &fac)
      : efac(fac), r(std::make_shared<op::boolop::TrivialSimplifier>(efac)) {}

  // Pre: exp is in NNF
  VisitAction operator()(Expr exp) {
    if (is_pos_bool_lit(exp)) {
      return VisitAction::skipKids();
    }

    if (isOpX<NEG>(exp)) {
      if (is_pos_bool_lit(exp->left())) {
        return VisitAction::doKids();
      } else {
        return VisitAction::changeTo(r->trueE);
      }
    }

    if (isOpX<AND>(exp) || isOpX<OR>(exp)) {
      return VisitAction::doKids();
    }

    if (isOpX<EQ>(exp)) {
      if (is_bool_lit(exp->left()) && is_bool_lit(exp->right())) {
        return VisitAction::doKids();
      }
    }

    // everything else abstracted to true
    return VisitAction::changeTo(r->trueE);
  }
};

static Expr preNNF(Expr exp) {
  op::boolop::BS<PreNNF> bs(new PreNNF());
  return dagVisit(bs, exp);
}

static Expr boolAbstraction(Expr exp) {
  exp = preNNF(exp);
  exp = op::boolop::nnf(exp);
  BA n(exp->efac());
  return dagVisit(n, exp);
}

void boolAbstraction(ExprVector &side, ExprVector &abs_side) {
  for (auto exp : side) {
    Expr bexp = boolAbstraction(exp);
    abs_side.push_back(bexp);
  }
  abs_side.erase(std::remove_if(abs_side.begin(), abs_side.end(),
                                [](Expr e) { return isOpX<TRUE>(e); }),
                 abs_side.end());
}

} // namespace path_bmc
} // namespace seahorn
