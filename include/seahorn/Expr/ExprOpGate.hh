/// Mutable Boolean gates
#pragma once
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprOpBool.hh"
namespace expr {

namespace op {
enum class GateOpKind { OUT_G, AND_G, OR_G, NEG_G };

struct GateOp : public expr::Operator {
  GateOpKind m_kind;
  GateOp(GateOpKind k) : expr::Operator(expr::OpFamilyId::GateOp), m_kind(k) {}
  virtual bool isMutable() const { return true; }
  static bool classof(expr::Operator const *op) {
    return op->getFamilyId() == expr::OpFamilyId::GateOp;
  }
};

/// an output gate
NOP(OUT_G, "OUT_G", PREFIX, GateOp, typeCheck::boolType::OneOrMore)
NOP(AND_G, "/\\", INFIX, GateOp, typeCheck::boolType::Nary);
NOP(OR_G, "\\/", INFIX, GateOp, typeCheck::boolType::Nary);
NOP(NEG_G, "~", PREFIX, GateOp, typeCheck::boolType::Unary);

namespace gate {
inline Expr land(Expr e1, Expr e2) {
  if (e1 == e2)
    return e1;

  if (isOpX<TRUE>(e1))
    return e2;
  if (isOpX<TRUE>(e2))
    return e1;
  if (isOpX<FALSE>(e1) || isOpX<FALSE>(e2))
    return mk<FALSE>(e1->efac());

  return mk<AND_G>(e1, e2);
}

inline Expr lor(Expr e1, Expr e2) {
  if (isOpX<FALSE>(e1))
    return e2;
  if (isOpX<FALSE>(e2))
    return e1;
  if (isOpX<TRUE>(e1) || isOpX<TRUE>(e2))
    return mk<TRUE>(e1->efac());
  return mk<OR_G>(e1, e2);
}

inline Expr lneg(Expr e1) {
  if (isOpX<TRUE>(e1))
    return mk<FALSE>(e1->efac());
  if (isOpX<FALSE>(e1))
    return mk<TRUE>(e1->efac());

  if (isOpX<NEG_G>(e1) || isOpX<NEG>(e1))
    return e1->left();

  return mk<NEG_G>(e1);
}
} // namespace gate
} // namespace op
}
