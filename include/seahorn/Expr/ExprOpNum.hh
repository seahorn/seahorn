/// Numeric Operators
#pragma once
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/TypeChecker.hh"
#include "seahorn/Expr/TypeCheckerUtils.hh"

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

static inline Expr returnType(Expr exp, TypeCheckerHelper &helper) {
  return helper.typeOf(exp->first());
}
struct Unary {
  // Return type: type of children
  // Possible types of children: INT_TY, REAL_TY, UNINT_TY
  static inline Expr inferType(Expr exp, TypeCheckerHelper &helper) {
    return typeCheck::unary<INT_TY, REAL_TY, UNINT_TY>(exp, helper, returnType);
  }
};

struct Binary {
  // Return type: type of children
  // Possible types of children: INT_TY, REAL_TY, UNINT_TY
  static inline Expr inferType(Expr exp, TypeCheckerHelper &helper) {
    return typeCheck::binary<INT_TY, REAL_TY, UNINT_TY>(exp, helper, returnType);
  }
};

struct Nary {
  // Return type: type of children
  // Possible types of children: INT_TY, REAL_TY, UNINT_TY
  static inline Expr inferType(Expr exp, TypeCheckerHelper &helper) {
    return typeCheck::nary<INT_TY, REAL_TY, UNINT_TY>(exp, helper, returnType);
  }
};
} // namespace numType
} // namespace typeCheck

// -- Numeric operators
NOP_BASE(NumericOp)

NOP(PLUS, "+", INFIX, NumericOp, typeCheck::numType::Nary)
NOP(MINUS, "-", INFIX, NumericOp, typeCheck::numType::Nary)
NOP(MULT, "*", INFIX, NumericOp, typeCheck::numType::Nary)
NOP(DIV, "/", INFIX, NumericOp, typeCheck::numType::Nary)
NOP(IDIV, "/", INFIX, NumericOp, typeCheck::numType::Nary)
NOP(MOD, "mod", INFIX, NumericOp, typeCheck::numType::Nary)
NOP(REM, "%", INFIX, NumericOp, typeCheck::numType::Nary)
NOP(UN_MINUS, "-", PREFIX, NumericOp, typeCheck::numType::Nary)
NOP(ABS, "abs", FUNCTIONAL, NumericOp, typeCheck::numType::Unary)

NOP(PINFTY, "oo", PREFIX, NumericOp, typeCheck::Any)
NOP(NINFTY, "-oo", PREFIX, NumericOp, typeCheck::Any)

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
NOP(ITV, "itv", numeric::ITV_PS, NumericOp, typeCheck::Any)
} // namespace op
} // namespace expr
