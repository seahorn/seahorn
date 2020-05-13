/**==-- Finite Maps Expr Tests --==*/
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN

#include "doctest.h"
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/HornClauseDB.hh"
#include "llvm/Support/raw_ostream.h"

using namespace std;
using namespace expr;
using namespace expr::op;
using namespace seahorn;

TEST_CASE("z3_api.test_HCDB") {

  ExprFactory efac;

  Expr x = bind::intConst(mkTerm<string>("x", efac));

  Expr iTy = mk<INT_TY>(efac);
  Expr bTy = mk<BOOL_TY>(efac);

  ExprVector ftype;
  ftype.push_back(iTy);
  ftype.push_back(bTy);

  Expr fdecl = bind::fdecl(mkTerm<string>("f", efac), ftype);
  Expr fapp = bind::fapp(fdecl, x);

  EZ3 z3(efac);
  ZFixedPoint<EZ3> fp(z3);
  ZParams<EZ3> params(z3); // see HornSolver.cc for more default values
  params.set(":engine", "spacer");
  params.set(":xform.slice", false);
  params.set(":xform.inline-linear", false);
  params.set(":xform.inline-eager", false);
  fp.set(params);

  HornClauseDB db(efac);

  Expr solution = mkTerm<expr::mpz_class>(42, efac);

  ExprVector vars;
  vars.push_back(x);

  ExprSet allVars;
  allVars.insert(vars.begin(), vars.end());

  ExprVector body;
  body.push_back(mk<EQ>(x, solution));

  db.registerRelation(fdecl);
  HornRule rule(allVars, fapp, body[0]); // f(x) <- x = 42.
  db.addRule(rule);

  ExprVector qvars;
  Expr query;

  // Actual query ?- x \= 42, f(x). %% unsat
  qvars.push_back(x);
  query = mk<AND>(mk<NEQ>(x, solution), fapp);

  // Register new relation to query without variables
  ExprVector qtype;
  qtype.push_back(bTy);
  Expr query_name = mkTerm<string>("query1", efac);
  Expr qdecl = bind::fdecl(query_name, qtype);

  // this line makes it crash, try uncommenting it
  // qdecl = bind::boolConst(query_name);

  db.registerRelation(qdecl);
  Expr q_head = bind::fapp(qdecl);
  Expr q_body = query;
  ExprSet auxVars;
  auxVars.insert(qvars.begin(), qvars.end());
  HornRule query_rule(auxVars, q_head, q_body);
  db.addRule(query_rule);

  db.addQuery(q_head);

  errs() << db << "\n";
  db.loadZFixedPoint(fp, true); // SkipConstraints = true

  errs() << "query: " << *q_head << "\nfp content:\n";
  errs() << fp.toString() << "\nend fp content\n";
  errs() << "Expected: unsat\n";
  boost::tribool res = fp.query();
  errs() << "Solving: " << (res ? "sat" : "unsat") << "\n";

  CHECK(!static_cast<bool>(res));

  // example with 1 literal:
  // f(x) :- x = 42.
  // query1 :- x /= 42, f(x).
  // UNSAT
}
