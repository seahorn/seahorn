#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/APInt.h"
#include "boost/lexical_cast.hpp"
#include "doctest.h"

TEST_CASE("expr.APInt") {
  using namespace expr;
  using namespace llvm;

  APInt numA(64, "30903631872", 10);
  mpz_class numZ = toMpz(numA);
  errs() << "numA: " << numA << "\n";
  errs() << "numZ: " << boost::lexical_cast<std::string>(numZ) << "\n";

  CHECK(numA.toString(10, false) == boost::lexical_cast<std::string>(numZ));

}

TEST_CASE("expr.APInt.large") {
  using namespace expr;
  using namespace llvm;

  APInt numA2(85, "453350497004842588831744", 10);
  mpz_class numZ2 = toMpz(numA2);
  errs() << "numA2: " << numA2 << "\n";
  errs() << "numZ2: " << boost::lexical_cast<std::string>(numZ2) << "\n";

  CHECK(numA2.toString(10, false) == boost::lexical_cast<std::string>(numZ2));
}
