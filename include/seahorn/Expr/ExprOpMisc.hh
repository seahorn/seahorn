#pragma once
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpCore.hh"

namespace expr {

namespace op {
enum class MiscOpKind { NONDET, ASM, TUPLE, CONS };

namespace typeCheck {
struct Cons : public TypeCheckBase {
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (exp->arity() > 2) // can be 1 for end node; 2 for normal node
      return sort::errorTy(exp->efac());
    return sort::anyTy(exp->efac());
  }
};
} // namespace typeCheck
// -- Not yet sorted operators
NOP_BASE(MiscOp)

/** A non-deterministic value */
NOP(NONDET, "nondet", FUNCTIONAL, MiscOp, typeCheck::Any)
/** An assumption */
NOP(ASM, "ASM", ADDRESS, MiscOp, typeCheck::Any)
/** A tupple */
NOP(TUPLE, "tuple", FUNCTIONAL, MiscOp, typeCheck::Any)
/* Cons array node */
NOP(CONS, "cons", FUNCTIONAL, MiscOp, typeCheck::Cons)
} // namespace op
} // namespace expr
