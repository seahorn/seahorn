// Bind error code, location and expression
#pragma once

#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/TypeCheckerErrors.hh"
#include "seahorn/Expr/TypeCheckerUtils.hh"

#define TYPE_ERR_LOC_INFO                                                      \
  "File: " __FILE__ ", Line: " + std::to_string(__LINE__)

namespace expr {
namespace op {
namespace bind {
struct ERRORBINDER {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    OS << "(";
    OS << name << " ";
    assert(args.size() >= 1);
    auto first = args.begin();
    auto code = getTerm<mpz_class>(*first).get_ui();
    const std::string errstr = GET_ERROR_STR((g_TyErrorCode)code);
    OS << errstr << " ";
    ++first;
    for (auto it = first, end = args.end(); it != end; ++it) {
      (*it)->Print(OS, depth + 2, true);
      if (it + 1 != end)
        OS << " ";
    }
    OS << ") ";
  }
};
} // namespace bind

namespace typeCheck {
namespace bindType {
struct ErrorBinder : public TypeCheckBase {
  /// ensures that: 1. all children except for the last (the body) are constants
  ///  2. the body type is BOOL_TY
  /// \note does not check bound variables
  /// \return BOOL_TY
  inline Expr inferType(Expr exp, TypeChecker &tc) override {
    return sort::errorTy(exp->efac());
  }
};
} // namespace bindType
} // namespace typeCheck
} // namespace op
enum class ErrorBinderOpKind { ERRORBINDER };
NOP_BASE(ErrorBinderOp)
/** Error binder */
NOP(ERRORBINDER, "ERRORBINDER", bind::ERRORBINDER, ErrorBinderOp,
    typeCheck::bindType::ErrorBinder)

// Make an error binding given
// 1. an error code,
// 2. location in typechecker (expr) codebase where error occurred, and,
// 3. the expression that caused the error
static Expr mkErrorBinding(g_TyErrorCode code, const std::string loc,
                           Expr badExp) {
  Expr codeE = mkTerm<expr::mpz_class>(code, badExp->efac());
  Expr locE = mkTerm<std::string>(loc, badExp->efac());
  return mk<ERRORBINDER>(codeE, locE, badExp);
}

} // namespace expr
