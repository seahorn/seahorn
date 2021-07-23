/// Boolean Operators
#pragma once
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/ExprOpSort.hh"
#include "seahorn/Expr/TypeChecker.hh"
#include "seahorn/Expr/TypeCheckerUtils.hh"

namespace expr {
namespace op {
enum class BoolOpKind { TRUE, FALSE, AND, OR, XOR, NEG, IMPL, ITE, IFF };

namespace typeCheck {
namespace boolType {

struct OneOrMore  : public TypeCheckBase{
  /// \return BOOL_TY
  /// Possible types of children: BOOL_TY
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::oneOrMore<BOOL_TY, BOOL_TY>(exp, tc);
  }
};

struct Unary  : public TypeCheckBase{
  /// \return BOOL_TY
  /// Possible types of children: BOOL_TY
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::unary<BOOL_TY, BOOL_TY>(exp, tc);
  }
};

struct Binary  : public TypeCheckBase{
  /// \return BOOL_TY
  /// Possible types of children: BOOL_TY
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::binary<BOOL_TY, BOOL_TY>(exp, tc);
  }
};

struct Nary  : public TypeCheckBase{
  /// \return BOOL_TY
  /// Possible types of children: BOOL_TY
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::nary<BOOL_TY, BOOL_TY>(exp, tc);
  }
};

struct ITE  : public TypeCheckBase{
  inline Expr inferType(Expr exp, TypeChecker &tc) {

    // ite(a,b,c) : a is bool type, b and c are the same type
    if (exp->arity() == 3 && isOp<BOOL_TY>(tc.typeOf(exp->arg(0))) &&
        (tc.typeOf(exp->arg(1)) == tc.typeOf(exp->arg(2))))
      return tc.typeOf(exp->arg(1));

    return sort::errorTy(exp->efac());
  }
};

struct TrueFalse  : public TypeCheckBase{
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    return sort::boolTy(exp->efac());
  }
};

} // namespace boolType
} // namespace typeCheck

// -- Boolean opearators
NOP_BASE(BoolOp)

/* operator definitions */
NOP(TRUE, "true", PREFIX, BoolOp, typeCheck::boolType::TrueFalse)
NOP(FALSE, "false", PREFIX, BoolOp, typeCheck::boolType::TrueFalse)
NOP(AND, "&&", INFIX, BoolOp, typeCheck::boolType::Nary)
NOP(OR, "||", INFIX, BoolOp, typeCheck::boolType::Nary)
NOP(XOR, "^", INFIX, BoolOp, typeCheck::boolType::Nary)
NOP(NEG, "!", PREFIX, BoolOp, typeCheck::boolType::Unary)
NOP(IMPL, "->", INFIX, BoolOp, typeCheck::boolType::Binary)
NOP(ITE, "ite", FUNCTIONAL, BoolOp, typeCheck::boolType::ITE)
NOP(IFF, "<->", INFIX, BoolOp, typeCheck::boolType::Binary)

namespace boolop {
// -- logical AND. Applies simplifications
inline Expr land(Expr e1, Expr e2) {
  if (e1 == e2)
    return e1;

  if (isOpX<TRUE>(e1))
    return e2;
  if (isOpX<TRUE>(e2))
    return e1;
  if (isOpX<FALSE>(e1) || isOpX<FALSE>(e2))
    return mk<FALSE>(e1->efac());

  return mk<AND>(e1, e2);
}

inline Expr lor(Expr e1, Expr e2) {
  if (isOpX<FALSE>(e1))
    return e2;
  if (isOpX<FALSE>(e2))
    return e1;
  if (isOpX<TRUE>(e1) || isOpX<TRUE>(e2))
    return mk<TRUE>(e1->efac());
  return mk<OR>(e1, e2);
}

inline Expr limp(Expr e1, Expr e2) {
  // TRUE -> x  IS x
  if (isOpX<TRUE>(e1))
    return e2;
  // x -> TRUE  IS TRUE
  if (isOpX<TRUE>(e2))
    return e2;
  // FALSE -> x IS TRUE
  if (isOpX<FALSE>(e1))
    return mk<TRUE>(e1->efac());
  // x -> x IS TRUE
  if (e1 == e2)
    return mk<TRUE>(e1->efac());

  // x -> FALSE is missing since it adds a negation

  return mk<IMPL>(e1, e2);
}

inline Expr lite(Expr c, Expr t, Expr e) {
  if (isOpX<TRUE>(c))
    return t;
  if (isOpX<FALSE>(c))
    return e;
  if (t == e)
    return t;

  return mk<ITE>(c, t, e);
}

inline Expr lneg(Expr e1) {
  if (isOpX<TRUE>(e1))
    return mk<FALSE>(e1->efac());
  if (isOpX<FALSE>(e1))
    return mk<TRUE>(e1->efac());

  if (isOpX<NEG>(e1))
    return e1->left();

  return mk<NEG>(e1);
}

template <typename R> Expr land(const R &r) {
  assert(std::begin(r) != std::end(r));

  // -- reduce unary AND to the operand
  if (boost::size(r) == 1)
    return *std::begin(r);

  auto &efac = (*std::begin(r))->efac();
  ExprVector res;
  for (auto e : r) {
    if (isOpX<FALSE>(e))
      return mk<FALSE>(efac);
    else if (!isOpX<TRUE>(e))
      res.push_back(e);
  }

  if (res.empty()) {
    return mk<TRUE>(efac);
  } else if (res.size() == 1) {
    return *(res.begin());
  } else {
    return mknary<AND>(res.begin(), res.end());
  }
}

unsigned circSize(Expr e);
unsigned circSize(const ExprVector &vec);

/**
 * Very simple simplifier for Boolean Operators
 */
Expr simplify(Expr exp);

/**
 * Very simple normalizer for AND/OR expressions
 */
Expr norm(Expr exp);

/** Gather binary Boolean operators into n-ary ones. Helps
    readability. Best done after NNF */
Expr gather(Expr exp);

/**
 * Converts to NNF. Assumes the only Boolean operators of exp

 * are AND/OR/NEG.
 */
Expr nnf(Expr exp);

/** Makes an expression pretty for printing */
Expr pp(Expr exp);

} // namespace boolop
} // namespace op
} // namespace expr
