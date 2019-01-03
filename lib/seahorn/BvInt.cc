/**
   Not used. Should be removed when deprecated expressions are removed.
 */
#include "ufo/deprecated/Expr.hpp"

using namespace expr;

namespace expr {
namespace op {
NOP(IABS, "I", PREFIX, MiscOp);

namespace abs {
inline Expr iabs(Expr v) { return mk<IABS>(v); }
inline bool is_iabs(Expr v) { return isOpX<IABS>(v); }
} // namespace abs
} // namespace op
} // namespace expr

namespace {
struct BvIntRewriter : public std::unary_function<Expr, Expr> {
  ExprFactory &m_efac;

  BvIntRewriter(ExprFactory &efac) : m_efac(efac) {}
  BvIntRewriter(const BvIntRewriter &o) : m_efac(o.m_efac) {}

  Expr operator()(Expr exp) {
    if (isOpX<BULT>(exp))
      return mk<LT>(exp->left(), exp->right());
    /// XXX handle special cases
    if (isOpX<BSLT>(exp))
      return mk<LT>(exp->left(), exp->right());
    if (isOpX<BULE>(exp))
      return mk<LEQ>(exp->left(), exp->right());
    if (isOpX<BSLE>(exp))
      return mk<LEQ>(exp->left(), exp->right());

    if (isOpX<BUGT>(exp))
      return mk<GT>(exp->left(), exp->right());
    if (isOpX<BSGT>(exp))
      return mk<GT>(exp->left(), exp->right());
    if (isOpX<BUGE>(exp))
      return mk<GEQ>(exp->left(), exp->right());
    if (isOpX<BSGE>(exp))
      return mk<GEQ>(exp->left(), exp->right());

    if (isOpX<BADD>(exp))
      return mk<PLUS>(exp->left(), exp->right());
    if (isOpX<BSUB>(exp))
      return mk<MINUS>(exp->left(), exp->right());
    if (isOpX<BMUL>(exp))
      return mk<MULT>(exp->left(), exp->right());
    if (isOpX<BUDIV>(exp))
      return mk<IDIV>(exp->left(), exp->right());
    if (isOpX<BSDIV>(exp))
      return mk<IDIV>(exp->left(), exp->right());
    if (isOpX<BUREM>(exp))
      return mk<REM>(exp->left(), exp->right());
    if (isOpX<BSREM>(exp))
      return mk<REM>(exp->left(), exp->right());
    if (isOpX<BSMOD>(exp))
      return mk<MOD>(exp->left(), exp->right());

    if (isOpX<BEXTRACT>(exp))
      return bv::earg(exp);
    if (isOpX<BSEXT>(exp))
      return exp->left();
    if (isOpX<BZEXT>(exp))
      return exp->left();

    if (isOpX<BV2INT>(exp))
      return exp->left();

    if (isOp<BvOp>(exp))
      return bind::intConst(abs::iabs(exp));

    return exp;
  }
};

struct BVINTABS : public std::unary_function<Expr, VisitAction> {
  ExprFactory &m_efac;
  /// side-condition
  ExprVector m_side;

  std::shared_ptr<BvIntRewriter> m_r;

  BVINTABS(const BVINTABS &o) : m_efac(o.m_efac), m_r(o.m_r) {}
  BVINTABS(ExprFactory &efac)
      : m_efac(efac), m_r(std::make_shared<BvIntRewriter>(m_efac)) {}

  Expr side() { return mknary<AND>(mk<TRUE>(m_efac), m_side); }

  VisitAction operator()(Expr exp) {
    /// bv numeral
    if (bv::is_bvnum(exp))
      return VisitAction::changeTo(exp->arg(0));

    /// constants
    if (bind::isFapp(exp) && exp->arity() == 1) {
      Expr fdecl = bind::fname(exp);
      assert(bind::domainSz(fdecl) == 0);
      Expr rangeTy = bind::rangeTy(fdecl);

      /// bv constant
      if (isOpX<BVSORT>(rangeTy))
        return VisitAction::changeTo(
            bind::intConst(abs::iabs(bind::fname(fdecl))));

      /// bv-array constant
      if (isOpX<ARRAY_TY>(rangeTy)) {
        Expr idxTy = sort::arrayIndexTy(rangeTy);
        Expr valTy = sort::arrayValTy(rangeTy);

        if (!isOpX<BVSORT>(idxTy) && !isOpX<BVSORT>(valTy))
          return VisitAction::skipKids();

        idxTy = isOpX<BVSORT>(idxTy) ? sort::intTy(m_efac) : idxTy;
        valTy = isOpX<BVSORT>(valTy) ? sort::intTy(m_efac) : valTy;

        rangeTy = sort::arrayTy(idxTy, valTy);
        return VisitAction::changeTo(
            bind::mkConst(bind::fname(fdecl), rangeTy));
      }

      return VisitAction::skipKids();
    }

    if (isOpX<INT2BV>(exp))
      return VisitAction::changeTo(exp->left());

    return VisitAction::changeDoKidsRewrite(exp, m_r);

    return VisitAction::skipKids();
  }
};
} // namespace

namespace seahorn {
/// Abstracts away bit-vector operations in the input
Expr bvIntAbstract(Expr v) {
  BVINTABS go(v->efac());
  Expr r = dagVisit(go, v);
  return boolop::land(r, go.side());
}

} // namespace seahorn
