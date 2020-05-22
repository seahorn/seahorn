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

namespace typeCheck {
namespace numType {

static inline bool isValidNumType(Expr exp) {
  if (exp != nullptr &&
      (isOp<INT_TY>(exp) || isOp<REAL_TY>(exp) || isOp<UNINT_TY>(exp)))
    return true;
  else
    return false;
}

// ensures: 1. correct number of children, 2. all children are of the correct
// type, 3. all children are of the same type
static inline Expr checkChildren(Expr exp,
                                 std::function<bool(Expr exp)> checkNumChildren,
                                 TypeChecker &tc) {
  if (!checkNumChildren(exp))
    return sort::errorTy(exp->efac());

  Expr type = tc.typeOf(exp->first());

  auto isSameType = [&tc, &type](Expr exp) {
    return type != nullptr && tc.typeOf(exp) == type;
  };

  if (isValidNumType(type) &&
      std::all_of(exp->args_begin(), exp->args_end(), isSameType))
    return type;
  else
    return sort::errorTy(exp->efac());
}

struct UNARY {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    std::function<bool(Expr)> checkNumChildren = [](Expr exp) -> bool {
      return exp->arity() == 1;
    };
    return checkChildren(exp, checkNumChildren, tc);
  }
};

struct NARY {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    std::function<bool(Expr)> checkNumChildren = [](Expr exp) -> bool {
      return exp->arity() >= 2;
    };
    return checkChildren(exp, checkNumChildren, tc);
  }
};
} // namespace numType
} // namespace typeCheck

// -- Numeric operators
NOP_BASE(NumericOp)

NOP_TYPECHECK(PLUS, "+", INFIX, NumericOp, typeCheck::numType::NARY)
NOP_TYPECHECK(MINUS, "-", INFIX, NumericOp, typeCheck::numType::NARY)
NOP_TYPECHECK(MULT, "*", INFIX, NumericOp, typeCheck::numType::NARY)
NOP_TYPECHECK(DIV, "/", INFIX, NumericOp, typeCheck::numType::NARY)
NOP_TYPECHECK(IDIV, "/", INFIX, NumericOp, typeCheck::numType::NARY)
NOP_TYPECHECK(MOD, "mod", INFIX, NumericOp, typeCheck::numType::NARY)
NOP_TYPECHECK(REM, "%", INFIX, NumericOp, typeCheck::numType::NARY)
NOP_TYPECHECK(UN_MINUS, "-", PREFIX, NumericOp, typeCheck::numType::NARY)
NOP_TYPECHECK(ABS, "abs", FUNCTIONAL, NumericOp, typeCheck::numType::UNARY)

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
