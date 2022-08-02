/**==-- Finite Maps in CHC Transformation Tests --==*/
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN

#include "doctest.h"

#include "doctest.h"
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/ExprOpBv.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/FiniteMapTransf.hh"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornClauseDBTransf.hh"
#include "llvm/Support/raw_ostream.h"

using namespace std;
using namespace expr;
using namespace expr::op;
using namespace seahorn;

static Expr mkIntKey(unsigned n, ExprFactory &efac) {
  return bind::intConst(
      mkTerm("k" + boost::lexical_cast<std::string>(n), efac));
}

static Expr mkBvKey(unsigned n, unsigned width, ExprFactory &efac) {
  return bv::bvConst(mkTerm("j" + boost::lexical_cast<std::string>(n), efac),
                     width);
}

static Expr mkFMapConstInt(const std::string name, const ExprVector ks) {
  ExprFactory &efac = ks.at(0)->efac();
  Expr finiteMapTy = sort::finiteMapTy(sort::intTy(efac), ks);
  Expr fmconst = bind::mkConst(mkTerm(name, efac), finiteMapTy);

  bind::IsConst ic;

  CHECK(ic(fmconst));
  return fmconst;
}

// -- versions with ExprVector by value so that the initialization with {}
// -- can be used directly in the arguments
static Expr mkConstFiniteMap(const ExprVector ks, Expr edefault,
                             const ExprVector vs) {
  return fmap::constFiniteMap(ks, edefault, vs);
}

static Expr mkConstFiniteMap(const ExprVector ks, Expr edefault) {
  ExprVector vs;

  for (int i = 0; i < ks.size(); i++)
    vs.push_back(edefault);

  return fmap::constFiniteMap(ks, edefault, vs);
}

static Expr mkIntConst(const std::string name, ExprFactory &efac) {
  return bind::intConst(mkTerm(name, efac));
}

static Expr mkBvConst(const std::string name, unsigned width,
                      ExprFactory &efac) {
  return bv::bvConst(mkTerm(name, efac), width);
}

static Expr mkInt(unsigned num, ExprFactory &efac) {
  return mkTerm<expr::mpz_class>(num, efac);
}

static Expr mkBvNum(mpz_class num, unsigned width, ExprFactory &efac) {
  return bv::bvnum(num, width, efac);
}

static Expr mkFun(const std::string &name, ExprVector sort) {
  return bind::fdecl(mkTerm(name, sort.at(0)->efac()), sort);
}

static Expr registerQueryHornClauseDB(Expr query, ExprSet qvars,
                                      HornClauseDB &db) {

  Expr qdecl = mkFun("query1", {sort::boolTy(db.getExprFactory())});
  Expr q = bind::fapp(qdecl);
  db.registerRelation(qdecl);
  db.addRule(qvars, boolop::limp(query, q));
  db.addQuery(q);
  return q;
}

static bool solveHornClauseDBZ3(HornClauseDB &db) {
  EZ3 z3(db.getExprFactory());
  ZFixedPoint<EZ3> fp(z3);
  ZParams<EZ3> params(z3); // see HornSolver.cc for more default values
  params.set(":engine", "spacer");
  params.set(":xform.slice", false);
  params.set(":xform.inline-linear", false);
  params.set(":xform.inline-eager", false);

  fp.set(params);

  db.loadZFixedPoint(fp, false /* SkipConstraints */);

  errs() << "\nfp content" << fp.toString() << "\n";
  boost::tribool res = fp.query();
  errs() << "Solving: " << (res ? "sat" : "unsat") << "\n";
  return static_cast<bool>(res);
}

TEST_CASE("expr.finite_map.test_map_type_HCDB") {

  ExprFactory efac;
  HornClauseDB db(efac);

  Expr bTy = sort::boolTy(efac);
  Expr iTy = sort::intTy(efac);

  ExprVector ks = {mkIntKey(1, efac)};
  Expr x = mkIntConst("x", efac);
  Expr map1 = mkFMapConstInt("map", ks);
  Expr solution = mkInt(42, efac);
  Expr fdecl = mkFun("f", {iTy, bTy});
  Expr fapp = bind::fapp(fdecl, x);
  db.registerRelation(fdecl);
  ExprVector body = {
      mk<EQ>(map1, mkConstFiniteMap(ks, mkInt(0, efac)), {mkInt(1, efac)}),
      mk<EQ>(x, solution)};
  ExprSet vars = {x};
  db.addRule(vars, boolop::limp(mknary<AND>(body), fapp));

  // ?- x \= 42, f(x). %% unsat
  registerQueryHornClauseDB(mk<AND>(mk<NEQ>(x, solution), fapp), vars, db);

  Expr bv32Ty = bv::bvsort(32, efac);
  Expr gdecl = mkFun("g", {bv32Ty, bTy});
  Expr gapp = bind::fapp(gdecl, x);
  Expr y = mkBvConst("y", 32, efac);
  Expr solutionBv = mkBvNum(42UL, 32, efac);
  ExprVector gbody = {mk<EQ>(map1, mkConstFiniteMap(ks, mkBvNum(0, 32, efac))),
                      mk<EQ>(x, solutionBv)};
  ExprSet varsBv = {y};
  // ?- y \= 42, g(y). %% unsat
  registerQueryHornClauseDB(mk<AND>(mk<NEQ>(y, solutionBv), gapp), varsBv, db);

  errs() << "HornClauseDB with maps\n";
  errs() << db << "\n";
  // This cannot be solved by Z3
}

Expr visit_body(ExprSet vars, Expr e, ExprFactory &efac,
                ZSimplifier<EZ3> &zsimp) {
  DagVisitCache dvc;
  FiniteMapBodyVisitor fmv(vars, efac, zsimp);
  errs() << "\nTesting visit:" << *e << " --------\n";
  Expr te = visit(fmv, e, dvc);
  errs() << "Transformed:" << *te << "\n";
  return te;
}

Expr visit_args(ExprSet vars, ExprFactory &efac, Expr e, ExprMap predTransf) {
  DagVisitCache dvc;
  FiniteMapArgsVisitor fmv(vars, predTransf, efac);
  errs() << "\nTesting visit:" << *e << " --------\n";
  Expr te = visit(fmv, e, dvc);
  errs() << "Transformed:" << *te << "\n";
  return te;
}

TEST_CASE("expr.finite_map.transf_1key") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);
  Expr v1 = mkIntConst("v1", efac);

  EZ3 z3(efac);
  ZSimplifier<EZ3> zsimp(z3);

  CHECK(k1 == visit_body({k1, v1}, k1, efac, zsimp));

  Expr map = mkConstFiniteMap({k1}, mkInt(0, efac), {mkInt(1, efac)});
  CHECK(map == visit_body({k1, v1}, map, efac, zsimp));

  Expr map_set = fmap::mkSet(map, k1, v1);
  CHECK(map_set != visit_body({k1, v1}, map_set, efac, zsimp));

  Expr map_get = fmap::mkGet(map_set, k1);
  CHECK(map_get != visit_body({k1, v1}, fmap::mkGet(map_set, k1), efac, zsimp));
}

TEST_CASE("expr.finite_map.fmap_2ks") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);
  Expr k2 = mkIntKey(2, efac);
  Expr v1 = mkIntConst("v1", efac);

  Expr map_set = fmap::set(mkConstFiniteMap({k1, k2}, mkInt(0, efac),
                                            {mkInt(1, efac), mkInt(2, efac)}),
                           k1, v1);

  EZ3 z3(efac);
  ZSimplifier<EZ3> zsimp(z3);

  CHECK(visit_body({k1, k2, v1}, mk<EQ>(v1, fmap::get(map_set, k1)), efac,
                   zsimp));
}

TEST_CASE("expr.finite_map.cmp_gets_fmap") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);
  Expr k2 = mkIntKey(2, efac);

  // transforming:
  // get(set(defk(k2,k1), k1, 30), k1) =  get(set(defk(k2), k2, 30), k2)
  Expr set2 =
      fmap::mkSet(mkConstFiniteMap({k2}, mkInt(0, efac)), k2, mkInt(40, efac));
  Expr set1 = fmap::mkSet(mkConstFiniteMap({k1, k2}, mkInt(0, efac)), k1,
                          mkInt(40, efac));
  EZ3 z3(efac);
  ZSimplifier<EZ3> zsimp(z3);

  CHECK(visit_body({k1, k2},
                   mk<EQ>(fmap::mkGet(set1, k1), fmap::mkGet(set2, k2)), efac,
                   zsimp));
  // SAT
}

TEST_CASE("expr.finite_map.fmap_eq") {

  ExprFactory efac;
  EZ3 z3(efac);
  ZSimplifier<EZ3> zsimp(z3);

  Expr k1 = mkIntKey(1, efac);
  Expr v1 = mkIntConst("v1", efac);
  Expr map_var1 = mkFMapConstInt("map1", {k1});

  Expr map_set = fmap::mkSet(mkConstFiniteMap({k1}, mkInt(0, efac)), k1, v1);
  Expr map_set_get = fmap::mkGet(map_set, k1);

  ExprSet vars = {k1, v1, map_var1};
  Expr map_eq = mk<EQ>(map_var1, map_set);
  // map1=set(defmap(defk(k1), fmap-default(0)), k1, v1))

  CHECK(visit_body(vars, map_eq, efac, zsimp));

  // v1 = get(map1, k1), map1=set(defmap(defk(k1), fmap-default(0)), k1, v1))
  Expr ne =
      visit_body(vars, mk<AND>(map_eq, mk<EQ>(fmap::mkGet(map_var1, k1), v1)),
                 efac, zsimp);
  CHECK(boost::lexical_cast<std::string>(z3_simplify(z3, ne)) != "false");
}

TEST_CASE("expr.finite_map.transf_body") {

  // Put clauses in the HCDB
  ExprFactory efac;
  HornClauseDB db(efac);

  ExprVector ks = {mkIntKey(1, efac)};
  Expr x = mkIntConst("x", efac);

  Expr fdecl = mkFun("f", {sort::intTy(efac), sort::boolTy(efac)});
  Expr fapp = bind::fapp(fdecl, x);

  Expr solution = mkInt(42, efac);
  Expr set = fmap::mkSet(mkConstFiniteMap(ks, mkInt(0, efac)), ks[0], solution);

  db.registerRelation(fdecl);
  // f(x) :- x = get(set(defmap(defk(k1), fmap-default(0)), k1, 42), k1).
  ExprSet allVars = {x, ks[0]};
  db.addRule(allVars, boolop::limp(mk<EQ>(x, fmap::mkGet(set, ks[0])), fapp));

  // ?- x \= 42, f(x).
  registerQueryHornClauseDB(mk<AND>(mk<NEQ>(x, solution), fapp), {x}, db);

  errs() << "HornClauseDB with fmaps\n";
  errs() << db << "\n";
  // This cannot be solved by Z3

  HornClauseDB tdb(efac), tdb2(efac);
  EZ3 z3(efac);

  removeFiniteMapsHornClausesTransf(db, tdb);
  removeFiniteMapsBodyHornClausesTransf(tdb, tdb2, z3);

  errs() << "HornClauseDB without fmaps\n";
  errs() << tdb2 << "\n";

  CHECK(!solveHornClauseDBZ3(tdb2));
  // UNSAT
}

TEST_CASE("expr.finite_map.transf_body_fmapvars") {

  ExprFactory efac;
  HornClauseDB db(efac);

  Expr k1 = mkIntKey(1, efac);
  Expr k2 = mkIntKey(2, efac);

  Expr fmap_var = mkFMapConstInt("map1", {k1, k2});

  CHECK(bind::isFiniteMapConst(fmap_var));

  Expr x = mkIntConst("x", efac);
  Expr fdecl = mkFun("f", {sort::intTy(efac), sort::boolTy(efac)});
  Expr fapp = bind::fapp(fdecl, x);
  Expr solution = mkInt(42, efac);

  Expr set =
      fmap::mkSet(mkConstFiniteMap({k1, k2}, mkInt(0, efac)), k1, solution);
  Expr get = fmap::mkGet(fmap_var, k1);
  ExprVector body = {mk<EQ>(fmap_var, set), mk<EQ>(x, get)};

  db.registerRelation(fdecl);
  // f(x) :- map1 = set(defk(k1,k2), k1, 42), x = get(map1, k1).
  ExprSet vars = {x, k1, k2, fmap_var};
  db.addRule(
      vars, boolop::limp(mk<AND>(mk<EQ>(fmap_var, set), mk<EQ>(x, get)), fapp));

  // ?- x \= 42, f(x). %% unsat
  registerQueryHornClauseDB(mk<AND>(mk<NEQ>(x, solution), bind::fapp(fdecl, x)),
                            {x}, db);

  errs() << "HornClauseDB with fmaps\n";
  errs() << db << "\n";
  // This cannot be solved by Z3

  HornClauseDB tdb(efac), tdb2(efac);
  EZ3 z3(efac);

  removeFiniteMapsHornClausesTransf(db, tdb);
  removeFiniteMapsBodyHornClausesTransf(tdb, tdb2, z3);
  errs() << "HornClauseDB without fmaps\n";
  errs() << tdb2 << "\n";

  errs() << "Expected: unsat\n";
  CHECK(!solveHornClauseDBZ3(tdb2));
}

TEST_CASE("expr.finite_map.trans_fmap_args") {

  ExprFactory efac;
  HornClauseDB db(efac);

  Expr k1 = mkIntKey(1, efac);
  Expr k2 = mkIntKey(2, efac);
  ExprVector ks = {k1, k2};

  Expr fmap_var = mkFMapConstInt("map1", ks);
  Expr x = mkIntConst("x", efac);

  Expr iTy = sort::intTy(efac);
  Expr bTy = sort::boolTy(efac);
  Expr fdecl = mkFun("f", {sort::finiteMapTy(iTy, ks), iTy, iTy, bTy});
  db.registerRelation(fdecl);

  // f(map_a, k1, x) :-
  //     map_a = defmap(defk(map_a!k1),defv(map_a!v1)),
  //     x = get(map_a, k1).
  ExprSet vars = {x, k1, fmap_var};
  Expr init_map = mk<EQ>(fmap_var, fmap::mkVal(fmap_var, 0));
  Expr get_expr = mk<EQ>(x, fmap::mkGet(fmap_var, ks[0]));
  Expr fapp = bind::fapp(fdecl, fmap_var, k1, x);
  db.addRule(vars, boolop::limp(boolop::land(init_map, get_expr), fapp));

  Expr solution = mkInt(42, efac);
  Expr set = fmap::mkSet(mkConstFiniteMap(ks, mkInt(0, efac)), k1, solution);
  ExprVector query = {mk<NEQ>(x, solution), bind::fapp(fdecl, set, k1, x)};
  // ?- x \= 42, f(set(defk(k1, k2), k1, 42), k1, x). (UNSAT)

  registerQueryHornClauseDB(mknary<AND>(query), {x, k1, k2}, db);
  errs() << "HornClauseDB with fmaps\n" << db << "\n";

  HornClauseDB tdb(efac), tdb2(efac);
  EZ3 z3(efac);

  removeFiniteMapsHornClausesTransf(db, tdb);
  removeFiniteMapsBodyHornClausesTransf(tdb, tdb2, z3);

  errs() << "HornClauseDB without fmaps\n" << tdb2 << "\n";

  CHECK(!solveHornClauseDBZ3(tdb2));
}

TEST_CASE("expr.finite_map.fmap_fdecl") {

  ExprFactory efac;
  ExprVector ks = {mkIntKey(1, efac), mkIntKey(2, efac)};

  Expr finiteMapTy1 = sort::finiteMapTy(sort::intTy(efac), ks);

  ks.push_back(mkIntKey(3, efac));
  ks.push_back(mkIntKey(4, efac));
  ks.push_back(mkIntKey(5, efac));
  Expr finiteMapTy2 = sort::finiteMapTy(bv::bvsort(32, efac), ks);

  Expr fdecl = mkFun("mrel", {finiteMapTy1, finiteMapTy2, sort::boolTy(efac)});
  errs() << "fdecl: " << *fdecl << "\n";

  Expr fdeclT = fmap::mkMapsDecl(fdecl);

  CHECK(fdeclT != nullptr);
  CHECK(fdeclT != fdecl);
  errs() << "fdecl transformed: " << *fdeclT << "\n";
}

TEST_CASE("expr.finite_map.no_fmap_fdecl") {

  ExprFactory efac;
  Expr fdecl = mkFun(
      "nofmap", {sort::intTy(efac), sort::realTy(efac), sort::boolTy(efac)});
  Expr fdeclT = fmap::mkMapsDecl(fdecl);

  CHECK(fdeclT != nullptr);
  CHECK(fdeclT == fdecl);
}

TEST_CASE("expr.finite_map.clause_rewriter") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);
  Expr k2 = mkIntKey(2, efac);

  Expr map1 = mkFMapConstInt("map1", {k1});
  Expr fdecl1 = mkFun("map_rel_test",
                      {bind::rangeTy(bind::fname(map1)), sort::boolTy(efac)});

  ExprMap predtransf;
  predtransf[fdecl1] = fmap::mkMapsDecl(fdecl1);

  Expr fapp1 = bind::fapp(fdecl1, {map1});
  Expr newE = visit_args({map1}, efac, fapp1, predtransf);

  CHECK(newE);
  CHECK(newE != fapp1);

  // ------------------------------------------------------------
  // change order, they should be the "same" fmap type
  Expr map2 = mkFMapConstInt("map2", {k1, k2});
  Expr fapp1_b = bind::fapp(fdecl1, {map2});
  newE = visit_args({map2, k1, k2}, efac, fapp1_b, predtransf);

  CHECK(newE);
  CHECK(newE != fapp1);

  // ------------------------------------------------------------
  // non-normalized call with map
  ExprVector ks = {k1, k2};
  fapp1_b = bind::fapp(fdecl1, {mkConstFiniteMap(ks, mkInt(0, efac))});
  newE = visit_args({map2, k1, k2}, efac, fapp1_b, predtransf);

  CHECK(newE);
  CHECK(newE != fapp1);
}

Expr test_rules_map_args(HornClauseDB &db, ExprVector &ks) {
  assert(!ks.empty());

  ExprFactory &efac = db.getExprFactory();

  Expr iTy = sort::intTy(efac);
  Expr bTy = sort::boolTy(efac);

  Expr k1 = ks[0];
  Expr v = mkIntConst("v", efac);
  Expr map_var = mkFMapConstInt("map", ks);
  Expr init_map_var = mk<EQ>(map_var, fmap::mkVal(map_var, 0));
  Expr get_map = mk<EQ>(v, fmap::mkGet(map_var, k1));

  ExprVector foo1_types = {bind::rangeTy(bind::fname(map_var)), iTy, iTy, bTy};
  // reused for foo2 & foo3

  Expr foo1_decl = mkFun("foo1", foo1_types);
  ExprVector foo1_app_args = {map_var, k1, v};
  Expr foo1_app = bind::fapp(foo1_decl, foo1_app_args);
  // cl1 foo1(map, k1, v) :-
  //    map = defmap(defk(map!k1),default(...),defv(map!k1)),
  //    v = get(map, k1).
  Expr cl1 = boolop::limp(boolop::land(init_map_var, get_map), foo1_app);

  Expr bar_decl = mkFun("bar", {bind::rangeTy(bind::fname(map_var)), bTy});

  Expr foo2_decl = mkFun("foo2", foo1_types);
  Expr foo2_app = bind::fapp(foo2_decl, foo1_app_args);
  // cl2 foo2(map, k1, v) :-
  //    map = defmap(defk(map!k1),default(...),defv(map!k1)),
  //    v = get(map, k1), bar(map).
  ExprVector body2({init_map_var, get_map, bind::fapp(bar_decl, map_var)});
  Expr cl2 = boolop::limp(boolop::land(body2), foo2_app);

  Expr mapA_var = mkFMapConstInt("mapA", ks);
  Expr init_mapA_var = mk<EQ>(mapA_var, fmap::mkVal(mapA_var, 0));
  Expr get_mapA = fmap::mkGet(mapA_var, k1);
  Expr set = fmap::mkSet(mapA_var, k1, mk<PLUS>(get_mapA, mkInt(1, efac)));
  Expr foo3_decl = mkFun("foo3", foo1_types);
  Expr foo3_app = bind::fapp(foo3_decl, foo1_app_args); // reusing foo1_args
  // cl3: foo(map, k1, x) :-
  //    mapA = defmap(defk(mapA!k1),default(...),defv(mapA!k1)),
  //    map = defmap(defk(map!k1),default(...),defv(map!k1)),
  //    bar(mapA),
  //    map = set(mapA, k1, (get(mapA, k1), 1)).
  ExprVector body3({init_map_var, init_mapA_var, bind::fapp(bar_decl, mapA_var),
                    mk<EQ>(map_var, set)});
  Expr cl3 = boolop::limp(boolop::land(body3), foo3_app);

  db.registerRelation(foo1_decl);
  db.registerRelation(foo2_decl);
  db.registerRelation(foo3_decl);
  db.registerRelation(bar_decl);

  ExprSet rule_vars(foo1_app_args.begin(), foo1_app_args.end());

  for (auto k_it : ks) {
    Expr var = k_it;
    rule_vars.insert(var);
  }

  db.addRule(rule_vars, cl1);
  db.addRule(rule_vars, cl2); // same vars as foo1
  rule_vars.insert(mapA_var);
  db.addRule(rule_vars, cl3);

  Expr solution = mkInt(42, efac);
  Expr mapVar = mkFMapConstInt("m", ks);
  ExprVector values = {solution};
  auto k_it = ++ks.begin();

  Expr zero = mkInt(0, efac);
  // initialize the rest of the map with 0
  while (k_it != ks.end()) {
    values.push_back(zero);
    k_it++;
  }

  ExprVector qargs = {mapVar, ks[0], v};
  ExprVector qBody = {mk<EQ>(mapVar, mkConstFiniteMap(ks, values[0], values)),
                      bind::fapp(foo2_decl, qargs), mk<NEQ>(v, solution)};

  ExprSet vars(qargs.begin(), qargs.end());
  for (auto it : ks)
    vars.insert(it);

  return registerQueryHornClauseDB(mknary<AND>(qBody), vars, db);
}

TEST_CASE("expr.finite_map.full_transf_1key") {

  ExprFactory efac;
  HornClauseDB db(efac);

  ExprVector ks = {mkIntKey(1, efac)};

  Expr query = test_rules_map_args(db, ks);

  errs() << "HornClauseDB with fmaps in args\n";
  errs() << db << "\n";

  HornClauseDB tdb(efac), tdb2(efac);
  EZ3 z3(efac);

  removeFiniteMapsHornClausesTransf(db, tdb);
  removeFiniteMapsBodyHornClausesTransf(tdb, tdb2, z3);

  errs() << "HornClauseDB without fmaps\n";
  errs() << tdb2 << "\n";
  // original query:
  // query :- m = defmap(defmap(defk(k1), fmap-default(0)), defv(42)),
  //          foo1(m, k1, v), v \= 42.
  // UNSAT

  CHECK(!solveHornClauseDBZ3(tdb2));
}

TEST_CASE("expr.finite_map.full_transf_2ks") {

  ExprFactory efac;
  HornClauseDB db(efac);
  ExprVector ks = {mkIntKey(1, efac), mkIntKey(2, efac)};

  Expr query = test_rules_map_args(db, ks);

  errs() << "HornClauseDB with fmaps  -------------------- \n";
  errs() << db << "\n";
  // This cannot be solved by Z3

  HornClauseDB tdb(efac), tdb2(efac);
  EZ3 z3(efac);

  removeFiniteMapsHornClausesTransf(db, tdb);
  removeFiniteMapsBodyHornClausesTransf(tdb, tdb2, z3);

  // Intermediate output:

  // cl1: FOO1(k1, |get(map,k1)|, k2, |get(map,k2)|, k1, v) :-
  //              // side condition
  //              map = defmap(defk(k1, k2), defv(|get(map,k1)|,
  //              |get(map,k2)|)))), v = get(map, k1).

  // cl2: FOO2(k1, |get(map,k1)|, k2, |get(map,k2)|, k1, v) :-
  //              // side condition
  //              map = defmap(defk(k1, k2), defv(|get(map,k1)|,
  //              |get(map,k2)|)))), v = get(map, k1),
  //              // duplicated bc in arguments
  //              map = defmap(defk(k1, k2), defv(|get(map,k1)|,
  //              |get(map,k2)|)))), bar(k1, |get(map,k1)|).

  // cl3: FOO3(k1, |get(map,k1)|, k2, |get(map,k2)|, k1, x) :-
  //               map = defmap(defk(k1, k2), defv(|get(map,k1)|,
  //               |get(map,k2)|)))) map = set(mapA, k1, +(get(mapA, k1), 1)),
  //               // original mapA = defmap(defk(k1, k2), defv(mapA!k1,
  //               mapA!k2)))), G(k1, mapA!k1, k2, mapA!k2).

  errs() << "HornClauseDB without fmaps   ------------ \n";
  errs() << tdb2 << "\n";

  CHECK(!solveHornClauseDBZ3(tdb2));
}

TEST_CASE("expr.simplifier") {
  ExprFactory efac;
  EZ3 z3(efac);
  // ZParams<EZ3> params(z3);
  // params.set("pull_cheap_ite", true);
  // params.set("ite_extra_rules", true);
  ZSimplifier<EZ3> zsimp(z3);
  zsimp.params().set("pull_cheap_ite", true);
  zsimp.params().set("ite_extra_rules", true);

  Expr k = mkIntConst("k", efac);
  Expr v1 = mkIntConst("v1", efac);
  Expr v2 = mkIntConst("v2", efac);
  Expr p = mkIntConst("p", efac);
  Expr oneE = mkInt(1, efac);

  Expr toSimp = mk<ITE>(
      mk<EQ>(oneE, mk<ITE>(mk<EQ>(k, p), oneE, mkInt(0, efac))), v1, v2);
  errs() << "before simp: " << *toSimp << "\n";
  errs() << "simplified: " << *zsimp.simplify(toSimp) << "\n";
}
