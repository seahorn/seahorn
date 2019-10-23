/// Numeric Operators
#pragma once
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"

namespace expr {

namespace op {
enum class NumericOpKind {
  PLUS,
  MINUS,
  MULT,
  DIV,
  IDIV,
  MOD,
  REM,
  UN_MINUS,
  ABS,
  PINFTY,
  NINFTY,
  ITV
};
// -- Numeric operators
NOP_BASE(NumericOp)

NOP(PLUS, "+", INFIX, NumericOp)
NOP(MINUS, "-", INFIX, NumericOp)
NOP(MULT, "*", INFIX, NumericOp)
NOP(DIV, "/", INFIX, NumericOp)
NOP(IDIV, "/", INFIX, NumericOp);
NOP(MOD, "mod", INFIX, NumericOp)
NOP(REM, "%", INFIX, NumericOp)
NOP(UN_MINUS, "-", PREFIX, NumericOp)
NOP(ABS, "abs", FUNCTIONAL, NumericOp)

NOP(PINFTY, "oo", PREFIX, NumericOp)
NOP(NINFTY, "-oo", PREFIX, NumericOp)

namespace numeric {
struct ITV_PS {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    OS << "[";
    args[0]->Print(OS, depth, false);
    OS << ",";
    args[1]->Print(OS, depth, false);
    OS << "]";
  }
};
} // namespace numeric
NOP(ITV, "itv", numeric::ITV_PS, NumericOp)
} // namespace op
}
