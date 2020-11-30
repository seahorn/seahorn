#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#include "doctest.h"

// Define the entry point for unit tests.
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprOpBv.hh"
#include "seahorn/Expr/ExprGmp.hh"

using namespace seahorn;
static Expr mkInt(unsigned num, ExprFactory &efac) {
  return mkTerm<expr::mpz_class>(num, efac);
}
static Expr mkIntConst(const std::string name, ExprFactory &efac) {
  return bind::intConst(mkTerm(name, efac));
}

static Expr mkBvConst(const std::string name, ExprFactory &efac, unsigned width) {
  return bv::bvConst(mkTerm(name, efac), width);
}
TEST_CASE("expr.simplifier") {
  ExprFactory efac;
  EZ3 z3(efac);
  ZSimplifier<EZ3> zsimp(z3);
  zsimp.params().set("pull_cheap_ite", true);
  zsimp.params().set("ite_extra_rules", true);

  Expr k = mkIntConst("k", efac);
  Expr v1 = mkIntConst("v1", efac);
  Expr v2 = mkIntConst("v2", efac);
  Expr p = mkIntConst("p", efac);
  Expr oneE = mkInt(1, efac);
  Expr toSimp = mk<ITE>(mk<EQ>(oneE,  mk<ITE>(mk<EQ>(k, p), oneE, mkInt(0, efac))), v1, v2);
  errs() << "before simp: " << *toSimp << "\n";
  errs() << "simplified: " << *zsimp.simplify(toSimp) << "\n";
}

TEST_CASE("expr.neg") {
  ExprFactory efac;
  EZ3 z3(efac);
  ZSimplifier<EZ3> zsimp(z3);


  unsigned w = 1;
  Expr x = mkBvConst("x", efac, 64);
  Expr one = bv::bvnum(1, 64, efac);

  // multiplication by -1 requires cast to signed
  Expr mone = bv::bvnum(-static_cast<signed>(w), 64, efac);
  // Expr mone =  bv::bvnum(mpz_class(w).neg(), 64, efac);
  Expr y = mk<BADD>(x, mone);
  Expr z = mk<BULE>(one, y);

  Expr res = mk<OR>(mk<EQ>(x, bv::bvnum(0, 64, efac)),
                    mk<BULE>(bv::bvnum(2, 64, efac), x));
  errs() << "before simp: " << *z << "\n";
  Expr sres = zsimp.simplify(z);
  errs() << "after simp: " << *sres << "\n";
  CHECK(res == sres);
}
