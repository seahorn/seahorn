/**==-- Type Checker Tests --==*/
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#include "doctest.h"
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/HornClauseDB.hh"
#include "llvm/Support/raw_ostream.h"

using namespace expr;
using namespace expr::op;
using namespace seahorn;

static Expr mkFun(const std::string &name, ExprVector sort) {
  return bind::fdecl(mkTerm(name, sort.at(0)->efac()), sort);
}
TEST_CASE("z3_api.test_HCDB") {

  ExprFactory efac;
  Expr iTy = mk<INT_TY>(efac);
  Expr bTy = mk<BOOL_TY>(efac);

  // -- ensures Expr::dump() is available during debugging
  iTy->dump();

  Expr x = bind::fapp(mkFun("x", {iTy}));
  Expr fdecl = mkFun("f", {iTy, bTy});
  Expr f_of_x = bind::fapp(fdecl, x);
  errs() << "f(x)  == " << *f_of_x << "\n";
  Expr sol = mkTerm<expr::mpz_class>(42, efac);

  HornClauseDB db(efac);
  db.registerRelation(fdecl);

  ExprVector vars = {x};
  ExprSet allVars(vars.begin(), vars.end());

  ExprVector body;
  body.push_back(mk<EQ>(x, sol));
  HornRule rule(allVars, f_of_x, body.at(0)); // f(x) <- x = 42.
  db.addRule(rule);

  // Register new relation to query without variables
  Expr qdecl = mkFun("query1", {bTy});
  db.registerRelation(qdecl);

  Expr qhead = bind::fapp(qdecl);
  // Actual query ?- x \= 42, f(x). %% unsat
  Expr qbody = mk<AND>(f_of_x, mk<NEQ>(x, sol));
  HornRule qrule(vars, qhead, qbody);
  db.addRule(qrule);
  db.addQuery(qhead);

  EZ3 z3(efac);
  ZFixedPoint<EZ3> fp(z3);
  ZParams<EZ3> params(z3); // see HornSolver.cc for more default values
  params.set(":engine", "spacer");
  params.set(":xform.slice", false);
  params.set(":xform.inline-linear", false);
  params.set(":xform.inline-eager", false);
  fp.set(params);

  errs() << "Horn DB\n" << db << "\n";
  db.loadZFixedPoint(fp, /* SkipConstraints */ true);

  errs() << "query: " << *qhead << "\n"
         << "fp content:\n"
         << fp.toString() << "\n"
         << "end fp content\n"
         << "fp printed another way:\n"
         << fp << "\n";

  errs() << "Expected: unsat\n";
  boost::tribool res = fp.query();
  errs() << "Solving: " << (res ? "sat" : "unsat") << "\n";

  CHECK(!static_cast<bool>(res));

  // example with 1 literal:
  // f(x) :- x = 42.
  // query1 :- x /= 42, f(x).
  // UNSAT
}
