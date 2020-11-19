#pragma once
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpCore.hh"

using namespace expr;

// utility functions for numeric Expr
// mpz, bvnum, UINT...
namespace expr {
namespace numeric {

/// \param[out] num the number/value of the expression
/// \return true if the expression was numeric
bool getNum(Expr exp, mpz_class &num);

// return true of exp is one of:
// MPZ, UINT or bvnum
bool isNumeric(Expr exp);

Expr convertToMpz(Expr exp);

} // namespace numeric
} // namespace expr