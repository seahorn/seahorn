#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Expr/ExprOpBinder.hh"

#include "llvm/Support/raw_ostream.h"

#include "doctest.h"

TEST_CASE("z3.lambdas_test") {
  using namespace std;
  using namespace seahorn;
  using namespace expr;
  using namespace expr::op;

  ExprFactory efac;

  Expr bv32Ty = bv::bvsort(32, efac);
  Expr arrTy = op::sort::arrayTy(bv32Ty, bv32Ty);
  Expr bv0 = bv::bvnum(0UL, 32, efac);
  Expr bv1 = bv::bvnum(1UL, 32, efac);
  Expr bv2 = bv::bvnum(2UL, 32, efac);
  Expr bvT = bv::bvConst(mkTerm<string>("t", efac), 32);
  Expr bvA = bv::bvConst(mkTerm<string>("a", efac), 32);

  Expr arr1 = bind::mkConst(mkTerm<string>("arr", efac), arrTy);
  Expr sel = op::array::select(arr1, bvT);
  Expr lmbd1 = bind::abs<LAMBDA>(std::array<Expr, 1>{bvT}, sel);

  ExprVector args;
  args.push_back(bvA);
  Expr cmp = mk<EQ>(bvA, bv2);
  Expr fappl = op::bind::fapp(lmbd1, args);
  Expr ite = boolop::lite(cmp, bv0, fappl);
  Expr lmbd2 = bind::abs<LAMBDA>(std::array<Expr, 1>{bvA}, ite);

  EZ3 z3(efac);

  errs() << "arr: " << *arr1 << "\t" << z3_to_smtlib(z3, arr1) << "\n";
  errs() << "arr_sort: " << *bind::sortOf(arr1) << "\n";
  errs() << "sel: " << *sel << "\t" << z3_to_smtlib(z3, sel) << "\n";
  errs() << "lmbd1: " << *lmbd1 << "\t" << z3_to_smtlib(z3, lmbd1) << "\n";
  errs() << "fappl: " << *fappl << "\t" << z3_to_smtlib(z3, fappl) << "\n";
  errs() << "lmbd2: " << *lmbd2 << "\t" << z3_to_smtlib(z3, lmbd2) << "\n";

//  Expr tmp = bind::betaReduce(lmd3, z);
//  errs() << "tmp: " << *tmp << "\n";
//
//  Expr tmp1 = bind::betaReduce(lmd2, x, y);
//  errs() << "tmp1: " << *tmp1 << "\n";
}
