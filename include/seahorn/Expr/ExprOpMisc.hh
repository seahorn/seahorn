#pragma once
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpCore.hh"

namespace expr {

namespace op {
enum class MiscOpKind { NONDET, ASM, TUPLE };
// -- Not yet sorted operators
NOP_BASE(MiscOp)

/** A non-deterministic value */
NOP(NONDET, "nondet", FUNCTIONAL, MiscOp)
/** An assumption */
NOP(ASM, "ASM", ADDRESS, MiscOp)
/** A tupple */
NOP(TUPLE, "tuple", FUNCTIONAL, MiscOp)
} // namespace op
} // namespace expr
