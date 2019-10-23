#include "seahorn/Expr/Smt/EZ3.hh"
#include "llvm/Support/raw_ostream.h"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "doctest.h"

TEST_CASE("z3.fapp_test") {
  using namespace std;
  using namespace seahorn;
  using namespace expr;
  using namespace expr::op;

  ExprFactory efac;

  Expr x = bind::intConst(mkTerm<string>("x", efac));
  Expr y = bind::intConst(mkTerm<string>("y", efac));
  Expr z = bind::intConst(mkTerm<string>("z", efac));

  Expr iTy = mk<INT_TY>(efac);
  Expr bTy = mk<BOOL_TY>(efac);

  ExprVector ftype;
  ftype.push_back(iTy);
  ftype.push_back(iTy);
  ftype.push_back(bTy);

  Expr fdecl = bind::fdecl(mkTerm<string>("f", efac), ftype);
  ExprVector args;
  args.push_back(x);
  args.push_back(y);

  Expr fapp = bind::fapp(fdecl, args);

  EZ3 z3(efac);

  errs() << "fapp: " << *fapp << "\n";
  errs() << "z3: " << z3_to_smtlib(z3, fapp) << "\n";
  CHECK(lexical_cast<string>(*fapp) == z3_to_smtlib(z3, fapp));

  Expr lmd = bind::abs<LAMBDA>(std::array<Expr, 1>{x}, fapp);
  errs() << "lmd: " << *lmd << "\n";

  Expr lmd2 = bind::abs<LAMBDA>(std::array<Expr, 2>{x, y}, fapp);
  errs() << "lmd2: " << *lmd2 << "\n"
         << "body: " << *bind::body(lmd2) << "\n";
  errs() << "lmd2_z3: " << z3_to_smtlib(z3, lmd2) << "\n"
         << "body: " << z3_to_smtlib(z3, bind::body(lmd2)) << "\n";

  Expr lmd3 = bind::abs<LAMBDA>(std::array<Expr, 1>{y}, lmd);
  errs() << "lmd3: " << *lmd3 << "\n";

  Expr tmp = bind::betaReduce(lmd3, z);
  errs() << "tmp: " << *tmp << "\n";

  Expr tmp1 = bind::betaReduce(lmd2, x, y);
  errs() << "tmp1: " << *tmp1 << "\n";
}
