#include "doctest.h"
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"
#include "seahorn/Expr/ExprOpSort.hh"
#include "seahorn/Expr/ExprVisitor.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/FiniteMapTransf.hh"
#include "seahorn/HornClauseDB.hh"
#include "llvm/Support/raw_ostream.h"

using namespace std;
using namespace expr;
using namespace expr::op;
using namespace seahorn;

TEST_CASE("expr.finite_map.test_map_ty") {

  ExprFactory efac;
  ExprVector keys;

  keys.push_back(mkTerm<std::string>("k1", efac));
  keys.push_back(mkTerm<std::string>("k2", efac));

  Expr finiteMapTy = op::sort::finiteMapTy(keys);
  errs() << "Map type: " << *finiteMapTy << "\n";

  Expr map1 = mkTerm<std::string>("map1", efac);
  Expr map_const = bind::mkConst(map1, finiteMapTy);
  errs() << "Map const: " << *map_const << "\n";

  CHECK(bind::isFiniteMapConst(map_const));

  Expr name = bind::fname(map_const);
  errs() << "map const name: " << *name << "\n";
  Expr rTy = bind::rangeTy(name);
  errs() << "map const type: " << *rTy << "\n";

  ExprVector types;
  types.push_back(finiteMapTy);
  Expr fdecl = bind::fdecl(mkTerm<string>("f", efac), types);
  errs() << *fdecl << "\n";

  HornClauseDB db(efac);
  db.registerRelation(fdecl);

  errs() << db << "\n";
}

Expr visit_and_print(FiniteMapTransVisitor & fmv, Expr e, DagVisitCache &dvc){

  errs() << "\nTesting visit:" << *e << "--------\n";
  Expr trans = visit(fmv, e);
  errs() << "Transformed:" << *trans << "\n";
  return trans;
}

TEST_CASE("expr.finite_map.fmap_1key") {

  ExprFactory efac;

  HornClauseDB db(efac); // not necessary, remove!!
  ExprSet vars;
  FiniteMapTransVisitor fmv(efac, db, vars);

  DagVisitCache dvc;

  Expr k1 = bind::intConst(mkTerm<std::string>("k1", efac));
  Expr v1 = bind::intConst(mkTerm<std::string>("v1", efac));
  vars.insert(k1);
  vars.insert(v1);

  visit(fmv, k1, dvc);

  ExprVector keys;
  keys.push_back(k1);

  Expr map = finite_map::constFiniteMap(keys);
  visit_and_print(fmv, map, dvc);

  Expr map_set = finite_map::set(map, k1, v1);

  dvc.clear();
  visit_and_print(fmv, map_set, dvc);

  Expr map_set_get = finite_map::get(map_set, k1);
  dvc.clear();
  visit_and_print(fmv, map_set_get, dvc);
}

TEST_CASE("expr.finite_map.fmap_2keys") {

  ExprFactory efac;

  HornClauseDB db(efac); // not necessary, remove!!
  ExprSet vars;
  FiniteMapTransVisitor fmv(efac, db, vars);

  DagVisitCache dvc;

  Expr k1 = bind::intConst(mkTerm<std::string>("k1", efac));
  vars.insert(k1);
  Expr k2 = bind::intConst(mkTerm<std::string>("k2", efac));
  vars.insert(k2);
  Expr v1 = bind::intConst(mkTerm<std::string>("v1", efac));
  vars.insert(v1);

  ExprVector keys;
  keys.push_back(k1);
  keys.push_back(k2);

  Expr map = finite_map::constFiniteMap(keys);
  Expr map_set = finite_map::set(map, k1, v1);
  Expr map_set_get = finite_map::get(map_set, k1);
  visit_and_print(fmv, mk<EQ>(v1, map_set_get), dvc);

}

TEST_CASE("expr.finite_map.cmp_gets_fmap") {

  ExprFactory efac;

  HornClauseDB db(efac); // not necessary, remove!!
  ExprSet vars;
  FiniteMapTransVisitor fmv(efac, db, vars);

  DagVisitCache dvc;

  Expr k1 = bind::intConst(mkTerm<std::string>("k1", efac));
  Expr k2 = bind::intConst(mkTerm<std::string>("k2", efac));
  vars.insert(k1);
  vars.insert(k2);

  // transforming:
  // get(set(defk(k2,k1), k1, 30), k1) =  get(set(defk(k2), k2, 30), k2)

  ExprVector keys;
  keys.push_back(k2);

  Expr set2 = finite_map::set(finite_map::constFiniteMap(keys), k2,
                              mkTerm<expr::mpz_class>(40, efac));

  keys.push_back(k1);
  Expr set1 = finite_map::set(finite_map::constFiniteMap(keys), k1,
                              mkTerm<expr::mpz_class>(40, efac));

  Expr eq = mk<EQ>(finite_map::get(set1, k1), finite_map::get(set2, k2));

  visit_and_print(fmv, eq, dvc);
  // SAT
}

// map unifications are not being transformed yet
TEST_CASE("expr.finite_map.fmap_eq" * doctest::skip(true)) {

  ExprFactory efac;

  HornClauseDB db(efac); // not necessary, remove!!
  ExprSet vars;
  FiniteMapTransVisitor fmv(efac, db, vars);

  DagVisitCache dvc;

  Expr k1 = bind::intConst(mkTerm<std::string>("k1", efac));
  vars.insert(k1);
  Expr v1 = bind::intConst(mkTerm<std::string>("v1", efac));
  vars.insert(v1);
  Expr map_var1 = mkTerm<std::string>("map1", efac); // not done yet
  vars.insert(map_var1);

  ExprVector keys;
  keys.push_back(k1);

  Expr map = finite_map::constFiniteMap(keys);
  Expr map_set = finite_map::set(map, k1, v1);
  Expr map_set_get = finite_map::get(map_set, k1);

  Expr map_eq = mk<EQ>(map_var1, map_set);
  dvc.clear();
  visit_and_print(fmv, map_eq, dvc);

  Expr v2 = bind::intConst(mkTerm<std::string>("x", efac));
  vars.insert(v2);

  Expr map_set_and_get =
      mk<AND>(map_eq, mk<EQ>(v2, finite_map::get(map_var1, k1)));
  dvc.clear();
  visit_and_print(fmv, map_set_get, dvc);
}

inline void set_params(EZ3 &z3, ZFixedPoint<EZ3> &fp) {

  ZParams<EZ3> params(z3); // see HornSolver.cc for more default values
  params.set(":engine", "spacer");
  params.set(":xform.slice", false);
  params.set(":xform.inline-linear", false);
  params.set(":xform.inline-eager", false);

  fp.set(params);
}

TEST_CASE("expr.finite_map.transformation1") {

  // Put clauses in the HCDB
  ExprFactory efac;

  ExprVector keys;

  Expr k1 = bind::intConst(mkTerm<string>("k1", efac));
  keys.push_back(k1);

  Expr mapTy = sort::finiteMapTy(keys);
  Expr iTy = sort::intTy(efac);
  Expr bTy = sort::boolTy(efac);

  Expr x = bind::intConst(mkTerm<string>("x", efac));

  ExprVector ftype;
  ftype.push_back(iTy);
  ftype.push_back(bTy);
  Expr fdecl = bind::fdecl(mkTerm<string>("f", efac), ftype);
  Expr fapp = bind::fapp(fdecl, x);

  EZ3 z3(efac);
  ZFixedPoint<EZ3> fp(z3);
  set_params(z3, fp);
  HornClauseDB db(efac);

  Expr solution = mkTerm<expr::mpz_class>(42, efac);

  ExprVector vars;
  vars.push_back(x);
  vars.push_back(k1);

  ExprSet allVars;
  allVars.insert(vars.begin(), vars.end());

  ExprVector body;
  Expr set =
      finite_map::set(finite_map::constFiniteMap(keys), keys[0], solution);
  Expr get = finite_map::get(set, keys[0]);
  body.push_back(mk<EQ>(x, get));
  // body.push_back(mk<EQ>(x, solution));

  db.registerRelation(fdecl);
  HornRule rule(allVars, fapp, mknary<AND>(body));
  db.addRule(rule);
  ExprVector qvars;
  Expr query;

  // Actual query ?- x \= 42, f(x). %% unsat
  qvars.push_back(x);
  query = mk<AND>(mk<NEQ>(x, solution), bind::fapp(fdecl, x));

  // Register new relation to query without variables
  ExprVector qtype;
  qtype.push_back(mk<BOOL_TY>(efac));
  Expr query_name = mkTerm<string>("query1", efac);
  Expr qdecl = bind::fdecl(query_name, qtype);
  db.registerRelation(qdecl);
  Expr q_head = bind::fapp(qdecl);
  Expr q_body = query;
  ExprSet auxVars;
  auxVars.insert(qvars.begin(), qvars.end());
  HornRule query_rule(allVars, q_head, q_body);
  db.addRule(query_rule);

  // query with auxiliary relation
  db.addQuery(q_head);
  errs() << "HornClauseDB with fmaps\n";
  errs() << db << "\n";
  // This cannot be solved by Z3

  transformFiniteMapsHornClauses(db, efac);

  errs() << "HornClauseDB without fmaps\n";
  errs() << db << "\n";

  db.loadZFixedPoint(fp, false); // SkipConstraints = false

  // errs() << "query: " << *q_head << "\nfp content:\n";
  errs() << fp.toString() << "\nend fp content\n";
  errs() << "Expected: unsat\n";
  boost::tribool res = fp.query();
  errs() << "Solving: " << (res ? "sat" : "unsat") << "\n";

  CHECK(!static_cast<bool>(res));
  // example with map operations in 1 literal:
  // f(x) :- x = get(set(defk(k1), k1, 42), k1).
  // query1 :- x /= 42, f(x).
  // UNSAT
}

TEST_CASE("expr.finite_map.transformation_fmapvars") {

  // Put clauses in the HCDB
  ExprFactory efac;

  ExprVector keys;

  Expr k1 = bind::intConst(mkTerm<string>("k1", efac));
  Expr k2 = bind::intConst(mkTerm<string>("k2", efac));

  keys.push_back(k1);
  keys.push_back(k2);

  Expr fmapTy = sort::finiteMapTy(keys);
  Expr iTy = sort::intTy(efac);
  Expr bTy = sort::boolTy(efac);

  Expr fmap_var = bind::mkConst(mkTerm<string>("map1", efac), fmapTy);

  CHECK(bind::isFiniteMapConst(fmap_var));

  Expr x = bind::intConst(mkTerm<string>("x", efac));

  ExprVector ftype;
  ftype.push_back(iTy);
  ftype.push_back(bTy);
  Expr fdecl = bind::fdecl(mkTerm<string>("f", efac), ftype);
  Expr fapp = bind::fapp(fdecl, x);

  EZ3 z3(efac);
  ZFixedPoint<EZ3> fp(z3);
  set_params(z3, fp);
  HornClauseDB db(efac);

  Expr solution = mkTerm<expr::mpz_class>(42, efac);

  ExprVector vars;
  vars.push_back(x);
  vars.push_back(k1);
  vars.push_back(k2);
  vars.push_back(fmap_var);

  ExprSet allVars;
  allVars.insert(vars.begin(), vars.end());

  ExprVector body;
  Expr set =
      finite_map::set(finite_map::constFiniteMap(keys), keys[0], solution);
  body.push_back(mk<EQ>(fmap_var, set));
  Expr get = finite_map::get(fmap_var, keys[0]);
  body.push_back(mk<EQ>(x, get));

  db.registerRelation(fdecl);
  HornRule rule(allVars, fapp, mknary<AND>(body));
  // f(x) :- map1 = set(defk(k1,k2), k1, 42), x = get(map1, k1).
  db.addRule(rule);
  ExprVector qvars;
  Expr query;

  // Actual query ?- x \= 42, f(x). %% unsat
  qvars.push_back(x);
  query = mk<AND>(mk<NEQ>(x, solution), bind::fapp(fdecl, x));

  // Register new relation to query without variables
  ExprVector qtype;
  qtype.push_back(mk<BOOL_TY>(efac));
  Expr query_name = mkTerm<string>("query1", efac);
  Expr qdecl = bind::fdecl(query_name, qtype);
  db.registerRelation(qdecl);
  Expr q_head = bind::fapp(qdecl);
  Expr q_body = query;
  ExprSet auxVars;
  auxVars.insert(qvars.begin(), qvars.end());
  HornRule query_rule(allVars, q_head, q_body);
  db.addRule(query_rule);

  // query with auxiliary relation
  db.addQuery(q_head);
  errs() << "HornClauseDB with fmaps\n";
  errs() << db << "\n";
  // This cannot be solved by Z3

  transformFiniteMapsHornClauses(db, efac);

  errs() << "HornClauseDB without fmaps\n";
  errs() << db << "\n";

  db.loadZFixedPoint(fp, false); // SkipConstraints = false

  // errs() << "query: " << *q_head << "\nfp content:\n";
  errs() << fp.toString() << "\nend fp content\n";
  errs() << "Expected: unsat\n";
  boost::tribool res = fp.query();
  errs() << "Solving: " << (res ? "sat" : "unsat") << "\n";

  CHECK(!static_cast<bool>(res));
  // example with map operations in 1 literal:
  // f(x) :- x = get(set(defk(k1), k1, 42), k1).
  // query1 :- x /= 42, f(x).
  // UNSAT
}
