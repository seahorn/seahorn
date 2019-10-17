#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprGmp.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/APInt.h"
#include "boost/lexical_cast.hpp"
#include "doctest.h"

inline expr::mpz_class toMpzE(const llvm::APInt &v) {
  // Based on:
  // https://llvm.org/svn/llvm-project/polly/trunk/lib/Support/GICHelper.cpp
  // return v.getSExtValue ();

  llvm::APInt abs;
  abs = v.isNegative() ? v.abs() : v;

  const uint64_t *rawdata = abs.getRawData();
  unsigned numWords = abs.getNumWords();

  // TODO: Check if this is true for all platforms.
  expr::mpz_class res;
  mpz_import(res.get_mpz_t(), numWords, -1, sizeof(uint64_t), 0, 0, rawdata);

  if (v.isNegative()) res.neg(); 
  return res;
}

TEST_CASE("expr.APInt") {
  using namespace expr;
  using namespace llvm;

  APInt numA(64, "30903631872", 10);
  expr::mpz_class numZ = toMpzE(numA);
  errs() << "numA: " << numA << "\n";
  errs() << "numZ: " << numZ.to_string() << "\n";

  CHECK(numA.toString(10, false) == numZ.to_string());

}

TEST_CASE("expr.APInt.large") {
  using namespace expr;
  using namespace llvm;

  APInt numA2(85, "453350497004842588831744", 10);
  expr::mpz_class numZ2 = toMpzE(numA2);
  errs() << "numA2: " << numA2 << "\n";
  errs() << "numZ2: " << numZ2.to_string() << "\n";

  CHECK(numA2.toString(10, false) == numZ2.to_string());
}
