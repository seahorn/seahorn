/// Numeric Operators
#pragma once
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/TypeChecker.hh"

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

namespace typeCheck {
namespace numType {
  template <Comparison compareType, unsigned int numChildren>
  static inline Expr getType(Expr exp, TypeChecker &tc) {
    if (checkNumChildren<compareType, numChildren>(exp) && correctType<INT_TY, REAL_TY, UNINT_TY>(exp->first(), tc) && sameType(exp, tc)) 
      return tc.typeOf(exp->first());
    else
      return sort::errorTy(exp->efac());
  }

struct Unary {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return getType<Equal, 1> (exp, tc);
  }
};

struct Nary {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return getType<GreaterEqual, 2> (exp, tc);
  }
};
} // namespace numType
} // namespace typeCheck

// -- Numeric operators
NOP_BASE(NumericOp)

NOP_TYPECHECK(PLUS, "+", INFIX, NumericOp, typeCheck::numType::Nary)
NOP_TYPECHECK(MINUS, "-", INFIX, NumericOp, typeCheck::numType::Nary)
NOP_TYPECHECK(MULT, "*", INFIX, NumericOp, typeCheck::numType::Nary)
NOP_TYPECHECK(DIV, "/", INFIX, NumericOp, typeCheck::numType::Nary)
NOP_TYPECHECK(IDIV, "/", INFIX, NumericOp, typeCheck::numType::Nary)
NOP_TYPECHECK(MOD, "mod", INFIX, NumericOp, typeCheck::numType::Nary)
NOP_TYPECHECK(REM, "%", INFIX, NumericOp, typeCheck::numType::Nary)
NOP_TYPECHECK(UN_MINUS, "-", PREFIX, NumericOp, typeCheck::numType::Nary)
NOP_TYPECHECK(ABS, "abs", FUNCTIONAL, NumericOp, typeCheck::numType::Unary)

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
} // namespace expr
