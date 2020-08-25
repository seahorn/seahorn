
#pragma once

#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprGmp.hh"
#include "seahorn/Expr/ExprOpBind.hh"
#include "seahorn/Expr/ExprOpBinder.hh"

#include <math.h>
#include <stdlib.h>

namespace expr {
namespace eval {
namespace evalUtils {

template <typename T> T zeroUpperBits(const T &num, unsigned numBits) {
  T mask = 0;

  for (int i = 0; i < numBits; i++) {
    mask = mask | ((((T)1) << i));
  }

  return num & mask;
}

template <typename T> T zeroLowerBits(const T &num, unsigned numBits) {
  return (num >> numBits) << numBits;
}

/// \return the number of bits that the number uses
template <typename T> unsigned occupiedWidth(const T &num) {
  return (unsigned)log2(num) + 1;
}

template <> unsigned occupiedWidth<mpz_class>(const mpz_class &num) {
  return num.sizeInBase(2);
}

} // namespace evalUtils
} // namespace eval
} // namespace expr
