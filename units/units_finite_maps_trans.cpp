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

Expr visit_and_print(FiniteMapBodyVisitor &fmv, Expr e, DagVisitCache &dvc) {

  errs() << "\nTesting visit:" << *e << "--------\n";
  Expr trans = visit(fmv, e);
  errs() << "Transformed:" << *trans << "\n";
  return trans;
}

TEST_CASE("expr.finite_map.transf_1key") {

  ExprFactory efac;

  HornClauseDB db(efac); // not necessary, remove!!
  ExprSet vars;
  FiniteMapBodyVisitor fmv(db, vars);

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
  FiniteMapBodyVisitor fmv(db, vars);

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
  FiniteMapBodyVisitor fmv(db, vars);

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
TEST_CASE("expr.finite_map.fmap_eq") {

  ExprFactory efac;

  HornClauseDB db(efac); // not necessary, remove!!
  ExprSet vars;
  FiniteMapBodyVisitor fmv(db, vars);

  DagVisitCache dvc;

  Expr k1 = bind::intConst(mkTerm<std::string>("k1", efac));
  vars.insert(k1);
  Expr v1 = bind::intConst(mkTerm<std::string>("v1", efac));
  vars.insert(v1);
  Expr mTy = sort::finiteMapTy(k1);
  Expr map_var1 = bind::mkConst(mkTerm<std::string>("map1", efac),mTy);
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

  // map1=set(defk(k1), k1, v1))
  Expr map_set_and_get =
      mk<AND>(map_eq, mk<EQ>(v2, finite_map::get(map_var1, k1)));
  dvc.clear();
  visit_and_print(fmv, map_set_and_get, dvc);
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

  removeFiniteMapsBodiesHornClausesTransf(db);

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
  // f(x) :- x = get(set(defk(k1), k1, 42), k1), g(y).
  // query1 :- x /= 42, f(x).
  // UNSAT
}

TEST_CASE("expr.finite_map.transformation_fmapvars" * doctest::skip(true)) {

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

  removeFiniteMapsBodiesHornClausesTransf(db);

  errs() << "HornClauseDB without fmaps\n";
  errs() << db << "\n";

  // UNCOMMENT  WHEN TAGS ARE FIXED
  // db.loadZFixedPoint(fp, false); // SkipConstraints = false

  // // errs() << "query: " << *q_head << "\nfp content:\n";
  // errs() << fp.toString() << "\nend fp content\n";
  // errs() << "Expected: unsat\n";
  // boost::tribool res = fp.query();
  // errs() << "Solving: " << (res ? "sat" : "unsat") << "\n";

  // CHECK(!static_cast<bool>(res));
  // example with map operations in 1 literal:
  // f(x) :- x = get(set(defk(k1), k1, 42), k1).
  // query1 :- x /= 42, f(x).
  // UNSAT
}

TEST_CASE("expr.finite_map.trans_fmap_args" * doctest::skip(true)) {

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
  Expr x = bind::intConst(mkTerm<string>("x", efac));

  ExprVector ftype;
  ftype.push_back(fmapTy); // map
  ftype.push_back(iTy);    // key
  ftype.push_back(iTy);    // value
  ftype.push_back(bTy);    // return type of relation
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
  vars.push_back(fmap_var);

  ExprSet allVars;
  allVars.insert(vars.begin(), vars.end());

  ExprVector body;

  Expr get = finite_map::get(fmap_var, keys[0]);
  body.push_back(mk<EQ>(x, get));
  // f(map_a, k1, x) :- x = get(map_a, k1), g(map_a).

  db.registerRelation(fdecl);
  HornRule rule(allVars, fapp, mknary<AND>(body));

  db.addRule(rule);
  ExprVector qvars, query, fargs;

  // Actual query: UNSAT
  // ?- x \= 42, f(set(defk(k1, k2), k1, 42), k1, x).
  Expr set =
      finite_map::set(finite_map::constFiniteMap(keys), keys[0], solution);
  fargs.push_back(set);
  fargs.push_back(k1);
  fargs.push_back(x);
  query.push_back(mk<NEQ>(x, solution));
  query.push_back(bind::fapp(fdecl, fargs));

  // query variables
  qvars.push_back(x);
  qvars.push_back(k1);
  qvars.push_back(k2);

  // Register new relation to query without variables
  ExprVector qtype;
  qtype.push_back(mk<BOOL_TY>(efac));
  Expr query_name = mkTerm<string>("query1", efac);
  Expr qdecl = bind::fdecl(query_name, qtype);
  db.registerRelation(qdecl);
  Expr q_head = bind::fapp(qdecl);
  Expr q_body = mknary<AND>(query);
  ExprSet auxVars;
  auxVars.insert(qvars.begin(), qvars.end());
  HornRule query_rule(allVars, q_head, q_body);
  db.addRule(query_rule);

  // query with auxiliary relation
  db.addQuery(q_head); // This cannot be solved by Z3
  errs() << "HornClauseDB with fmaps\n" << db << "\n";

  removeFiniteMapsBodiesHornClausesTransf(db);

  errs() << "HornClauseDB without fmaps\n" << db << "\n";

  // UNCOMMENT  WHEN TAGS ARE FIXED
  // db.loadZFixedPoint(fp, false); // SkipConstraints = false

  // // errs() << "query: " << *q_head << "\nfp content:\n";
  // errs() << fp.toString() << "\nend fp content\n";
  // errs() << "Expected: unsat\n";
  // boost::tribool res = fp.query();
  // errs() << "Solving: " << (res ? "sat" : "unsat") << "\n";

  // CHECK(!static_cast<bool>(res));
  // example with map operations in 1 literal:
  // f(map_a, k1, x) :- x = get(map_a, k1).
  // query1 :- x /= 42, map = set(defk(k1, k2), k1, 42), f(map, k1, x).
  // UNSAT
}

TEST_CASE("expr.finite_map.trans_fmap_var_args" * doctest::skip(true)) {

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

  // f(map_a, k1, x) :- x = get(map_a, k1).
  // ?- x \= 42, map = set(defk(k1, k2), k1, 42), f(map, k1, x).
}

TEST_CASE("expr.finite_map.trans_fmap_fdecl") {

  ExprFactory efac;
  ExprVector keys;

  Expr bTy = sort::boolTy(efac);

  keys.push_back(mkTerm<std::string>("k1", efac));
  keys.push_back(mkTerm<std::string>("k2", efac));
  Expr finiteMapTy1 = op::sort::finiteMapTy(keys);

  keys.push_back(mkTerm<std::string>("k3", efac));
  keys.push_back(mkTerm<std::string>("k4", efac));
  keys.push_back(mkTerm<std::string>("k5", efac));
  Expr finiteMapTy2 = op::sort::finiteMapTy(keys);

  Expr fname = mkTerm<std::string>("map_relation", efac);
  ExprVector ftype;
  ftype.push_back(finiteMapTy1);
  ftype.push_back(finiteMapTy2); // TODO: include other types (e.g. array,
  ftype.push_back(bTy);          // bool,bv)

  Expr fdecl = bind::fdecl(fname, ftype);
  errs() << "fdecl: " << *fdecl << "\n";

  Expr fdeclT = processMapsDecl(fdecl, efac);

  CHECK(fdeclT != nullptr);
  errs() << "fdecl transformed: " << *fdeclT << "\n";
}

TEST_CASE("expr.finite_map.fapp_type_checker") {

  ExprFactory efac;
  ExprVector keys;

  Expr bTy = sort::boolTy(efac);

  keys.push_back(mkTerm<std::string>("k1", efac));
  Expr finiteMapTy1 = op::sort::finiteMapTy(keys);
  Expr map1 = bind::mkConst(mkTerm<std::string>("map1", efac), finiteMapTy1);

  keys.clear(); // change order, they should be the "same" fmap type
  keys.push_back(mkTerm<std::string>("k2", efac));
  keys.push_back(mkTerm<std::string>("k1", efac));
  Expr finiteMapTy1b = op::sort::finiteMapTy(keys);
  Expr map1b = bind::mkConst(mkTerm<std::string>("map1b", efac), finiteMapTy1);

  Expr fname = mkTerm<std::string>("map_relation", efac);

  ExprVector ftypes;
  ftypes.push_back(finiteMapTy1);
  ftypes.push_back(bTy);
  Expr fdecl1 = bind::fdecl(fname, ftypes);
  errs() << "fdecl: " << *fdecl1 << "\n";

  ExprVector fargs;
  fargs.push_back(map1);
  Expr fapp1 = bind::fapp(fdecl1, fargs);
  fargs[0] = map1b;
  Expr fapp1_b = bind::fapp(fdecl1, fargs);

  keys.clear();
  keys.push_back(mkTerm<std::string>("k3", efac));
  keys.push_back(mkTerm<std::string>("k4", efac));
  keys.push_back(mkTerm<std::string>("k5", efac));
  Expr finiteMapTy2 = op::sort::finiteMapTy(keys);
  Expr map2 = bind::mkConst(mkTerm<std::string>("map2", efac), finiteMapTy1);
  fargs[0] = map2;

  Expr fapp2 = bind::fapp(fdecl1, fargs);
  // this should violate an assertion

}

// I commented the code of this naive type checker, it only works when there is
// a map in both sides of the equality
TEST_CASE("expr.finite_map.eq_type_checker" * doctest::skip(true)) {

  ExprFactory efac;

  // Expr fmapTy = sort::finiteMapTy(keys);
  Expr iTy = sort::intTy(efac);
  Expr bTy = sort::boolTy(efac);

  // Expr fmap_var = bind::mkConst(mkTerm<string>("map1", efac), fmapTy);
  Expr x = bind::intConst(mkTerm<string>("x", efac));
  Expr b = bind::boolConst(mkTerm<string>("b", efac));

  Expr eq = mk<EQ>(x, b);
  Expr eqType = bind::type(eq);
  // errs() << "EQ type of: " << *eq << " is " << *eqType << "\n";

  HornClauseDB db(efac);
  ExprSet vars;

  vars.insert(x);
  vars.insert(b);

  FiniteMapBodyVisitor fmbv(db,vars);

  Expr e1 = visit(fmbv, eq);
}

TEST_CASE("expr.finite_map.head_rewriter") {

  ExprFactory efac;
  ExprVector keys;

  Expr bTy = sort::boolTy(efac);

  keys.push_back(mkTerm<std::string>("k1", efac));
  Expr finiteMapTy1 = op::sort::finiteMapTy(keys);
  Expr map1 = bind::mkConst(mkTerm<std::string>("map1", efac), finiteMapTy1);

  Expr fname = mkTerm<std::string>("map_rel_test", efac);

  ExprVector ftypes;
  ftypes.push_back(finiteMapTy1);
  ftypes.push_back(bTy);
  Expr fdecl1 = bind::fdecl(fname, ftypes);
  errs() << "fdecl: " << *fdecl1 << "\n";

  ExprVector fargs;
  fargs.push_back(map1);

  Expr fapp1 = bind::fapp(fdecl1, fargs);
  Expr newdecl = processMapsDecl(fdecl1, efac);

  ExprSet vars;
  vars.insert(map1);
  ExprVector unifs;
  errs() << "fapp one key:" << *fapp1 << "\n";

  Expr newfapp = headFiniteMapRewriter(fapp1, newdecl, vars, efac, unifs);
  errs() << "New fapp:\n";
  errs() << *newfapp << "\n";

  errs() << "New unifs:\n";
  for(auto e : unifs)
    errs() << "\t"<< *e << "\n";

  CHECK(!unifs.empty());

  // ------------------------------------------------------------
  keys.clear(); // change order, they should be the "same" fmap type
  keys.push_back(mkTerm<std::string>("k2", efac));
  keys.push_back(mkTerm<std::string>("k1", efac));
  Expr finiteMapTy1b = op::sort::finiteMapTy(keys);
  Expr map1b = bind::mkConst(mkTerm<std::string>("map1b", efac), finiteMapTy1);
  fargs[0] = map1b;

  unifs.clear();
  vars.clear();
  vars.insert(map1b);
  vars.insert(keys[0]);
  vars.insert(keys[1]);
  Expr fapp1_b = bind::fapp(fdecl1, fargs);
  errs() << "fapp two keys:" << *fapp1_b << "\n";

  newfapp = headFiniteMapRewriter(fapp1_b, newdecl, vars, efac, unifs);
  errs() << "New fapp:\n";
  errs() << *newfapp << "\n";

  errs() << "New unifs:\n";
  for (auto e : unifs)
    errs() << "\t" << *e << "\n";

  CHECK(!unifs.empty());

  // ------------------------------------------------------------
  fargs[0] = map1b;

  unifs.clear();
  vars.clear();
  vars.insert(keys[0]);
  vars.insert(keys[1]);

  fargs[0] = finite_map::constFiniteMap(keys);

  fapp1_b = bind::fapp(fdecl1, fargs);
  errs() << "fapp two keys no variable:" << *fapp1_b << "\n";

  newfapp = headFiniteMapRewriter(fapp1_b, newdecl, vars, efac, unifs);
  errs() << "New fapp:\n";
  errs() << *newfapp << "\n";

  errs() << "New unifs:\n";
  for (auto e : unifs)
    errs() << "\t" << *e << "\n";

  CHECK(!unifs.empty());

  // ------------------------------------------------------------
  // keys.clear();
  // keys.push_back(mkTerm<std::string>("k3", efac));
  // keys.push_back(mkTerm<std::string>("k4", efac));
  // keys.push_back(mkTerm<std::string>("k5", efac));
  // Expr finiteMapTy2 = op::sort::finiteMapTy(keys);
  // Expr map2 = bind::mkConst(mkTerm<std::string>("map2", efac), finiteMapTy1);
  // fargs[0] = map2;

  // Expr fapp2 = bind::fapp(fdecl1, fargs);
    // this should violate an assertion
}

void test_rules_map_args(HornClauseDB &db, ExprVector & keys) {
  ExprFactory &efac = db.getExprFactory();

  Expr iTy = sort::intTy(efac);
  Expr bTy = sort::boolTy(efac);

  Expr key1 = keys[0]; // mkTerm<std::string>("k1", efac);
  Expr fmapTy = sort::finiteMapTy(keys);

  Expr k1 = bind::intConst(key1);
  Expr v = bind::intConst(mkTerm<std::string>("v", efac));
  Expr map_var = bind::mkConst(mkTerm<std::string>("map", efac), fmapTy);

  Expr get_map = mk<EQ>(v, finite_map::get(map_var, k1));

  ExprVector foo1_types;
  foo1_types.push_back(fmapTy); // map
  foo1_types.push_back(iTy);    // key
  foo1_types.push_back(iTy);    // value
  foo1_types.push_back(bTy);    // return

  Expr foo1_decl =
      bind::fdecl(mkTerm<std::string>("foo1", efac), foo1_types);
  ExprVector foo1_app_args;
  foo1_app_args.push_back(map_var);
  foo1_app_args.push_back(k1);
  foo1_app_args.push_back(v);
  Expr foo1_app = bind::fapp(foo1_decl, foo1_app_args);

  // cl1 foo1(map, k1, v) :- v = get(map, k1).
  Expr cl1 = boolop::limp(get_map,foo1_app);

  ExprVector bar_types;
  bar_types.push_back(fmapTy);
  bar_types.push_back(bTy);
  Expr bar_decl = bind::fdecl(mkTerm<std::string>("bar", efac), bar_types);
  Expr bar_app = bind::fapp(bar_decl, map_var);

  Expr foo2_decl = bind::fdecl(mkTerm<std::string>("foo2", efac), foo1_types);
  Expr foo2_app = bind::fapp(foo2_decl, foo1_app_args); // reusing foo1_args

  // cl2 foo2(map, k1, v) :- v = get(map, k1), bar(map).
  Expr cl2 = boolop::limp(mk<AND>(get_map, bar_app), foo2_app);

  Expr mapA_var = bind::mkConst(mkTerm<std::string>("mapA", efac), fmapTy);
  Expr get_mapA = finite_map::get(mapA_var, k1);
  bind::fapp(bar_decl, map_var);
  Expr set =
      finite_map::set(mapA_var, k1,
                      mk<PLUS>(get_mapA, mkTerm<expr::mpz_class>(1, efac)));
  Expr barA_app = bind::fapp(bar_decl, mapA_var);
  ExprVector cl3_body;
  cl3_body.push_back(mk<EQ>(map_var, set));
  cl3_body.push_back(barA_app);

  Expr foo3_decl = bind::fdecl(mkTerm<std::string>("foo3", efac), foo1_types);
  Expr foo3_app = bind::fapp(foo3_decl, foo1_app_args); // reusing foo1_args

  Expr cl3 = boolop::limp(mknary<AND>(cl3_body), foo3_app);
  // cl3: foo(map, k1, x) :- map = set(mapA, k1, +(get(mapA, k1), 1)),
  //                         bar(mapA).

  db.registerRelation(foo1_decl);
  db.registerRelation(foo2_decl);
  db.registerRelation(foo3_decl);
  db.registerRelation(bar_decl);

  db.addRule(foo1_app_args, cl1);
  db.addRule(foo1_app_args, cl2); // same vars as foo1
  foo1_app_args.push_back(mapA_var);
  db.addRule(foo1_app_args, cl3);

}

TEST_CASE("expr.finite_map.remove_map_arguments") {

  ExprFactory efac;

  HornClauseDB db(efac);

  ExprVector keys;
  keys.push_back(mkTerm<std::string>("k1", efac));

  test_rules_map_args(db, keys);
  // generates: with map containing only k1

  // cl1 foo1(map, k1, v) :- v = get(map, k1).

  // cl2 foo2(map, k1, v) :- v = get(map, k1), bar(map).

  // cl3: foo(map, k1, x) :- map = set(mapA, k1, +(get(mapA, k1), 1)),
  //                         bar(mapA).

  errs() << "HornClauseDB with fmaps in args\n";
  errs() << db << "\n";
  // This cannot be solved by Z3

  removeFiniteMapsArgsHornClausesTransf(db);

  // desired output:

  // cl1: FOO1(k1, map!k1, k1, v) :-
  //              map = defmap(defk(k1), defv(map!k1)), // side condition
  //              v = get(map, k1).

  // cl2: FOO2(k1, map!k1, k1, v) :-
  //              map = defmap(defk(k1), defv(map!k1)), // side condition
  //              v = get(map, k1),
  //              // duplicated bc in arguments
  //              map = defmap(defk(k1), defv(map!k1)),
  //              twice bar(k1, map!k1).

  // cl3: FOO3(k1, map!k1, k1, x) :-
  //               map = defmap(defk(k1), defv(map!k1)), // side condition
  //               map = set(mapA, k1, +(get(mapA, k1), 1)), // original
  //               mapA = defmap(defk(k1), defv(mapA!k1)) // side condition
  //               for G G(mapA!k1, k1).

  errs() << "HornClauseDB without fmaps in args\n";
  errs() << db << "\n";
  // This cannot be solved by Z3

  // now apply local transformation only to the bodies
  // removeFiniteMapsBodiesHornClausesTransf(db);

  // errs() << "HornClauseDB without fmaps\n";
  // errs() << db << "\n";
  // This should be solvable by Z3
}

TEST_CASE("expr.finite_map.remove_map_arguments_2keys") {

  ExprFactory efac;

  HornClauseDB db(efac);

  ExprVector keys;
  keys.push_back(mkTerm<std::string>("k1", efac));
  keys.push_back(mkTerm<std::string>("k2", efac));

  test_rules_map_args(db, keys);
  // generates: with map containing only k1

  // cl1 foo1(map, k1, v) :- v = get(map, k1).

  // cl2 foo2(map, k1, v) :- v = get(map, k1), bar(map).

  // cl3: foo(map, k1, x) :- map = set(mapA, k1, +(get(mapA, k1), 1)),
  //                         bar(mapA).

  errs() << "HornClauseDB with fmaps in args\n";
  errs() << db << "\n";
  // This cannot be solved by Z3

  removeFiniteMapsArgsHornClausesTransf(db);

  // desired output:

  // cl1: FOO1(k1, map!k1, k2, map!k2, k1, v) :-
  //              // side condition
  //              map = defmap(defk(k1, k2), defv(map!k1, map!k2)))),
  //              v = get(map, k1).

  // cl2: FOO2(k1, map!k1, k2, map!k2, k1, v) :-
  //              // side condition
  //              map = defmap(defk(k1, k2), defv(map!k1, map!k2)))),
  //              v = get(map, k1),
  //              // duplicated bc in arguments
  //              map = defmap(defk(k1, k2), defv(map!k1, map!k2)))),
  //              bar(k1, map!k1).

  // cl3: FOO3(k1, map!k1, k2, map!k2, k1, x) :-
  //               map = defmap(defk(k1, k2), defv(map!k1, map!k2))))
  //               map = set(mapA, k1, +(get(mapA, k1), 1)), // original
  //               mapA = defmap(defk(k1, k2), defv(mapA!k1, mapA!k2)))),
  //               G(k1, mapA!k1, k2, mapA!k2).

  errs() << "HornClauseDB without fmaps in args\n";
  errs() << db << "\n";
  // This cannot be solved by Z3

  // now apply local transformation only to the bodies
  // removeFiniteMapsBodiesHornClausesTransf(db);

  // errs() << "HornClauseDB without fmaps\n";
  // errs() << db << "\n";
  // This should be solvable by Z3
}
