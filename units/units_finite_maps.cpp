/**==-- Finite Maps Expr Tests --==*/
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN

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

static Expr mkFMapConstInt(const std::string name, const ExprVector keys) {
  ExprFactory &efac = keys.at(0)->efac();
  Expr finiteMapTy = sort::finiteMapTy(sort::intTy(efac), keys);
  return bind::mkConst(mkTerm(name, efac), finiteMapTy);
}

// -- version with the ExprVector by value so that the initialization with {}
// -- can be used directly in the arguments
static Expr mkConstFiniteMap(const ExprVector keys, Expr edefault) {
  return finite_map::constFiniteMap(keys, edefault);
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

// -- version with the ExprVector by value so that the initialization with {}
// -- can be used directly in the arguments
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

TEST_CASE("expr.finite_map.create_map") {

  ExprFactory efac;
  Expr map = mkConstFiniteMap({mkIntKey(1, efac)}, mkInt(0, efac));

  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "defmap(defk(k1), fmap-default(0))");

  map = mkConstFiniteMap({mkBvKey(1, 32, efac)}, mkBvNum(0, 64, efac));

  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "defmap(defk(j1), fmap-default(0:bv(64)))");
}

TEST_CASE("expr.finite_map.set") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);
  Expr map = finite_map::set(mkConstFiniteMap({k1}, mkInt(0, efac)), k1,
                             mkInt(30, efac));

  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "set(defmap(defk(k1), fmap-default(0)), k1, 30)");
}

TEST_CASE("expr.finite_map.get") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);
  Expr eget = finite_map::get(mkConstFiniteMap({k1}, mkInt(0, efac)), k1);

  CHECK(eget);
  CHECK(boost::lexical_cast<std::string>(*eget) ==
        "get(defmap(defk(k1), fmap-default(0)), k1)");
}

TEST_CASE("expr.finite_map.create_set_3") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);
  Expr k2 = mkIntKey(2, efac);
  Expr k3 = mkIntKey(3, efac);

  Expr map = mkConstFiniteMap({k1, k2, k3}, mkInt(0, efac));
  map = finite_map::set(map, k1, mkInt(31, efac));

  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "set(defmap(defk(k1, k2, k3), fmap-default(0)), k1, 31)");

  map = finite_map::set(map, k2, mkInt(32, efac));
  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "set(set(defmap(defk(k1, k2, k3), fmap-default(0)), k1, 31), k2, 32)");

  map = finite_map::set(map, k3, mkInt(33, efac));
  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "set(set(set(defmap(defk(k1, k2, k3), fmap-default(0)), k1, 31), k2, "
        "32), k3, 33)");
}

TEST_CASE("expr.finite_map.create_keys_lambda") {

  ExprFactory efac;

  ExprVector keys = {mkIntKey(1, efac)};

  Expr lambda_keys = finite_map::mkKeys(keys, efac);
  CHECK(boost::lexical_cast<std::string>(lambda_keys) ==
        "(lambda (INT) ite(k1=(B0:INT), 1, 0))");

  keys.push_back(mkIntKey(2, efac));
  lambda_keys = finite_map::mkKeys(keys, efac);

  CHECK(boost::lexical_cast<std::string>(lambda_keys) ==
        "(lambda (INT) ite(k2=(B0:INT), 2, ite(k1=(B0:INT), 1, 0)))");

  keys.push_back(mkIntKey(3, efac));
  lambda_keys = finite_map::mkKeys(keys, efac);

  CHECK(boost::lexical_cast<std::string>(lambda_keys) ==
        "(lambda (INT) ite(k3=(B0:INT), 3, ite(k2=(B0:INT), 2, "
        "ite(k1=(B0:INT), 1, 0))))");
}

TEST_CASE("expr.finite_map.mkSetVal") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);
  ExprVector keys = {k1, mkIntKey(2, efac), mkIntKey(3, efac)};
  Expr lambda_keys = finite_map::mkKeys(keys, efac);
  CHECK(boost::lexical_cast<std::string>(lambda_keys) ==
        "(lambda (INT) ite(k3=(B0:INT), 3, ite(k2=(B0:INT), 2, "
        "ite(k1=(B0:INT), 1, 0))))");

  Expr map = finite_map::mkEmptyMap(mkInt(0, efac));
  // set the value of k1
  map = finite_map::mkSetVal(map, lambda_keys, k1, mkInt(42, efac), efac);

  CHECK(boost::lexical_cast<std::string>(map) ==
        "(lambda (INT) ite((B0:INT)=ite(k3=k1, 3, ite(k2=k1, 2, ite(k1=k1, 1, "
        "0))), 42, 0))");

  errs() << "map: " << *map << "\n";
  EZ3 z3(efac);
  errs() << "Simplified: " << *z3_simplify(z3, map) << "\n";
}

TEST_CASE("expr.finite_map.get_after_mkSetVal") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);
  ExprVector keys = {k1, mkIntKey(2, efac), mkIntKey(3, efac)};

  Expr lambda_keys = finite_map::mkKeys(keys, efac);
  CHECK(boost::lexical_cast<std::string>(lambda_keys) ==
        "(lambda (INT) ite(k3=(B0:INT), 3, ite(k2=(B0:INT), 2, "
        "ite(k1=(B0:INT), 1, 0))))");

  Expr map = finite_map::mkEmptyMap(mkInt(0, efac)); // init map
  map = finite_map::mkSetVal(map, lambda_keys, k1, mkInt(42, efac), efac);

  CHECK(boost::lexical_cast<std::string>(map) ==
        "(lambda (INT) ite((B0:INT)=ite(k3=k1, 3, ite(k2=k1, 2, ite(k1=k1, 1, "
        "0))), 42, 0))");

  Expr get_value = finite_map::mkGetVal(map, lambda_keys, k1);

  CHECK(boost::lexical_cast<std::string>(get_value) ==
        "ite(ite(k3=k1, 3, ite(k2=k1, 2, ite(k1=k1, 1, 0)))=ite(k3=k1, 3, "
        "ite(k2=k1, 2, ite(k1=k1, 1, 0))), 42, 0)");

  EZ3 z3(efac);

  errs() << "map: " << *map << "\n";
  errs() << "Simplified: " << *z3_simplify(z3, get_value) << "\n";

  CHECK(boost::lexical_cast<std::string>(
            z3_simplify(z3, mk<EQ>(get_value, mkInt(42, efac)))) == "true");
}

TEST_CASE("expr.finite_map.mkInitializedMap") {

  ExprFactory efac;
  EZ3 z3(efac);

  ExprVector keys = {mkIntKey(11, efac), mkIntKey(12, efac),
                     mkIntKey(13, efac)};
  ExprVector values = {mkInt(41, efac), mkInt(42, efac), mkInt(43, efac)};

  Expr lmdKeys = finite_map::mkKeys(keys, efac);
  Expr lmdValues = finite_map::mkInitializedMap(keys, sort::intTy(efac), values,
                                                lmdKeys, efac);

  Expr u_map = finite_map::constFiniteMap(keys, values); // uninterpreted map

  errs() << "lmdKeys:    " << *lmdValues << "\n\n";
  errs() << "lmdValues:    " << *lmdValues << "\n\n";

  for (int i = 0; i < keys.size(); i++) {
    Expr get_value = finite_map::mkGetVal(lmdValues, lmdKeys, keys[i]);
    Expr to_simp_true = mk<EQ>(get_value, values[i]);
    // cannot be simplified if constructed in a batch
    Expr simp = z3_simplify(z3, to_simp_true);
    errs() << "simplifying: "
           << *mk<EQ>(finite_map::get(u_map, keys[i]), values[i]) << "\n";
    errs() << "orig:        " << *to_simp_true << "\n";
    errs() << "simplified:  " << *simp << "\n\n";
    CHECK(boost::lexical_cast<std::string>(simp) != "false");
  }
}
TEST_CASE("expr.finite_map.fm_type_declaration") {

  ExprFactory efac;
  ExprVector keys = {mkIntKey(1, efac)};
  Expr fmTy = sort::finiteMapTy(sort::intTy(efac), keys);
  errs() << "Finite map type: " << fmTy << "\n";
  CHECK(isOpX<FINITE_MAP_TY>(fmTy));
  CHECK(isOpX<FINITE_MAP_KEYS_TY>(finite_map::keys(fmTy)));

  keys.push_back(mkIntKey(5, efac));
  fmTy = sort::finiteMapTy(bv::bvsort(64, efac), keys);
  errs() << "Finite map type: " << fmTy << "\n";

  CHECK(isOpX<FINITE_MAP_TY>(fmTy));
  CHECK(isOpX<FINITE_MAP_KEYS_TY>(finite_map::keys(fmTy)));
}

// same as map_in_body_1key but using HornClauseDB
TEST_CASE("expr.finite_map.test_map_type_HCDB") {

  ExprFactory efac;
  HornClauseDB db(efac);

  Expr bTy = sort::boolTy(efac);
  Expr iTy = sort::intTy(efac);

  ExprVector keys = {mkIntKey(1, efac)};
  Expr x = mkIntConst("x", efac);
  Expr map1 = mkFMapConstInt("map", keys);
  Expr solution = mkInt(42, efac);
  Expr fdecl = mkFun("f", {iTy, bTy});
  Expr fapp = bind::fapp(fdecl, x);
  db.registerRelation(fdecl);
  ExprVector body = {mk<EQ>(map1, mkConstFiniteMap(keys, mkInt(0, efac))),
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
  ExprVector gbody = {
      mk<EQ>(map1, mkConstFiniteMap(keys, mkBvNum(0, 32, efac))),
      mk<EQ>(x, solutionBv)};
  ExprSet varsBv = {y};
  // ?- y \= 42, g(y). %% unsat
  registerQueryHornClauseDB(mk<AND>(mk<NEQ>(y, solutionBv), gapp), varsBv, db);

  errs() << "HornClauseDB with maps\n";
  errs() << db << "\n";
  // This cannot be solved by Z3
}

Expr visit_body(ExprSet vars, Expr e, ExprFactory &efac) {
  DagVisitCache dvc;
  FiniteMapBodyVisitor fmv(vars, efac);
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

  CHECK(k1 == visit_body({k1, v1}, k1, efac));

  Expr map = mkConstFiniteMap({k1}, mkInt(0, efac));
  CHECK(map == visit_body({k1, v1}, map, efac));

  Expr map_set = finite_map::set(map, k1, v1);
  CHECK(map_set != visit_body({k1, v1}, map_set, efac));

  Expr map_get = finite_map::get(map_set, k1);
  CHECK(map_get != visit_body({k1, v1}, finite_map::get(map_set, k1), efac));
}

TEST_CASE("expr.finite_map.fmap_2keys") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);
  Expr k2 = mkIntKey(2, efac);
  Expr v1 = mkIntConst("v1", efac);

  Expr map_set =
      finite_map::set(mkConstFiniteMap({k1, k2}, mkInt(0, efac)), k1, v1);

  CHECK(
      visit_body({k1, k2, v1}, mk<EQ>(v1, finite_map::get(map_set, k1)), efac));
}

TEST_CASE("expr.finite_map.cmp_gets_fmap") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);
  Expr k2 = mkIntKey(2, efac);

  // transforming:
  // get(set(defk(k2,k1), k1, 30), k1) =  get(set(defk(k2), k2, 30), k2)
  Expr set2 = finite_map::set(mkConstFiniteMap({k2}, mkInt(0, efac)), k2,
                              mkInt(40, efac));
  Expr set1 = finite_map::set(mkConstFiniteMap({k1, k2}, mkInt(0, efac)), k1,
                              mkInt(40, efac));
  CHECK(visit_body({k1, k2},
                   mk<EQ>(finite_map::get(set1, k1), finite_map::get(set2, k2)),
                   efac));
  // SAT
}

TEST_CASE("expr.finite_map.fmap_eq") {

  ExprFactory efac;
  EZ3 z3(efac);

  Expr k1 = mkIntKey(1, efac);
  Expr v1 = mkIntConst("v1", efac);
  Expr map_var1 = mkFMapConstInt("map1", {k1});

  Expr map_set =
      finite_map::set(mkConstFiniteMap({k1}, mkInt(0, efac)), k1, v1);
  Expr map_set_get = finite_map::get(map_set, k1);

  ExprSet vars = {k1, v1, map_var1};
  Expr map_eq = mk<EQ>(map_var1, map_set);
  // map1=set(defmap(defk(k1), fmap-default(0)), k1, v1))
  CHECK(visit_body(vars, map_eq, efac));

  // v1 = get(map1, k1), map1=set(defmap(defk(k1), fmap-default(0)), k1, v1))
  Expr ne = visit_body(
      vars, mk<AND>(map_eq, mk<EQ>(finite_map::get(map_var1, k1), v1)), efac);
  CHECK(boost::lexical_cast<std::string>(z3_simplify(z3, ne)) != "false");
}

TEST_CASE("expr.finite_map.transf_body") {

  // Put clauses in the HCDB
  ExprFactory efac;
  HornClauseDB db(efac);

  ExprVector keys = {mkIntKey(1, efac)};
  Expr x = mkIntConst("x", efac);

  Expr fdecl = mkFun("f", {sort::intTy(efac), sort::boolTy(efac)});
  Expr fapp = bind::fapp(fdecl, x);

  Expr solution = mkInt(42, efac);
  Expr set = finite_map::set(mkConstFiniteMap(keys, mkInt(0, efac)), keys[0],
                             solution);

  db.registerRelation(fdecl);
  // f(x) :- x = get(set(defmap(defk(k1), fmap-default(0)), k1, 42), k1).
  ExprSet allVars = {x, keys[0]};
  db.addRule(allVars,
             boolop::limp(mk<EQ>(x, finite_map::get(set, keys[0])), fapp));

  // ?- x \= 42, f(x).
  registerQueryHornClauseDB(mk<AND>(mk<NEQ>(x, solution), fapp), {x}, db);

  errs() << "HornClauseDB with fmaps\n";
  errs() << db << "\n";
  // This cannot be solved by Z3

  HornClauseDB tdb(efac);
  removeFiniteMapsHornClausesTransf(db, tdb);

  errs() << "HornClauseDB without fmaps\n";
  errs() << tdb << "\n";

  CHECK(!solveHornClauseDBZ3(tdb));
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
      finite_map::set(mkConstFiniteMap({k1, k2}, mkInt(0, efac)), k1, solution);
  Expr get = finite_map::get(fmap_var, k1);
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

  HornClauseDB tdb(efac);
  removeFiniteMapsHornClausesTransf(db, tdb);
  errs() << "HornClauseDB without fmaps\n";
  errs() << tdb << "\n";

  errs() << "Expected: unsat\n";
  CHECK(!solveHornClauseDBZ3(tdb));
}

// TODO: add args transformation
TEST_CASE("expr.finite_map.trans_fmap_args" * doctest::skip(true)) {

  ExprFactory efac;
  HornClauseDB db(efac);

  Expr k1 = mkIntKey(1, efac);
  Expr k2 = mkIntKey(2, efac);
  ExprVector keys = {k1, k2};

  Expr fmap_var = mkFMapConstInt("map1", keys);
  Expr x = mkIntConst("x", efac);

  Expr iTy = sort::intTy(efac);
  Expr bTy = sort::boolTy(efac);
  Expr fdecl = mkFun("f", {sort::finiteMapTy(iTy, keys), iTy, iTy, bTy});
  db.registerRelation(fdecl);

  // f(map_a, k1, x) :- x = get(map_a, k1).
  ExprSet vars = {x, k1, fmap_var};
  Expr fapp = bind::fapp(fdecl, fmap_var, k1, x);
  db.addRule(vars, boolop::limp(finite_map::get(fmap_var, keys[0]), fapp));

  Expr solution = mkInt(42, efac);
  Expr set =
      finite_map::set(mkConstFiniteMap(keys, mkInt(0, efac)), k1, solution);
  ExprVector query = {mk<NEQ>(x, solution), bind::fapp(fdecl, set, k1, x)};
  // ?- x \= 42, f(set(defk(k1, k2), k1, 42), k1, x). (UNSAT)

  registerQueryHornClauseDB(mknary<AND>(query), {x, k1, k2}, db);
  errs() << "HornClauseDB with fmaps\n" << db << "\n";

  HornClauseDB tdb(efac);
  removeFiniteMapsHornClausesTransf(db, tdb);
  errs() << "HornClauseDB without fmaps\n" << tdb << "\n";

  CHECK(!solveHornClauseDBZ3(tdb));
}

TEST_CASE("expr.finite_map.fmap_fdecl") {

  ExprFactory efac;
  ExprVector keys = {mkIntKey(1, efac), mkIntKey(2, efac)};

  Expr finiteMapTy1 = sort::finiteMapTy(sort::intTy(efac), keys);

  keys.push_back(mkIntKey(3, efac));
  keys.push_back(mkIntKey(4, efac));
  keys.push_back(mkIntKey(5, efac));
  Expr finiteMapTy2 = sort::finiteMapTy(bv::bvsort(32, efac), keys);

  Expr fdecl = mkFun("mrel", {finiteMapTy1, finiteMapTy2, sort::boolTy(efac)});
  errs() << "fdecl: " << *fdecl << "\n";

  Expr fdeclT = finite_map::mkMapsDecl(fdecl, efac);

  CHECK(fdeclT != nullptr);
  CHECK(fdeclT != fdecl);
  errs() << "fdecl transformed: " << *fdeclT << "\n";
}

TEST_CASE("expr.finite_map.no_fmap_fdecl") {

  ExprFactory efac;
  Expr fdecl = mkFun(
      "nofmap", {sort::intTy(efac), sort::realTy(efac), sort::boolTy(efac)});
  Expr fdeclT = finite_map::mkMapsDecl(fdecl, efac);

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
  predtransf[fdecl1] = finite_map::mkMapsDecl(fdecl1, efac);

  Expr fapp1 = bind::fapp(fdecl1, {map1});
  Expr newE = visit_args({map1}, efac, fapp1, predtransf);

  CHECK(newE);
  CHECK(newE != fapp1);
  CHECK(isOpX<AND>(newE));

  // ------------------------------------------------------------
  // change order, they should be the "same" fmap type
  Expr map2 = mkFMapConstInt("map2", {k1, k2});
  Expr fapp1_b = bind::fapp(fdecl1, {map2});
  newE = visit_args({map2, k1, k2}, efac, fapp1_b, predtransf);

  CHECK(newE);
  CHECK(newE != fapp1);
  CHECK(isOpX<AND>(newE));

  // ------------------------------------------------------------
  // non-normalized call with map
  ExprVector keys = {k1, k2};
  fapp1_b = bind::fapp(fdecl1, {mkConstFiniteMap(keys, mkInt(0, efac))});
  newE = visit_args({map2, k1, k2}, efac, fapp1_b, predtransf);

  CHECK(newE);
  CHECK(newE != fapp1);
  CHECK(isOpX<AND>(newE));
}

Expr test_rules_map_args(HornClauseDB &db, ExprVector &keys) {
  assert(!keys.empty());

  ExprFactory &efac = db.getExprFactory();

  Expr iTy = sort::intTy(efac);
  Expr bTy = sort::boolTy(efac);

  Expr k1 = keys[0];
  Expr v = mkIntConst("v", efac);
  Expr map_var = mkFMapConstInt("map", keys);

  Expr get_map = mk<EQ>(v, finite_map::get(map_var, k1));

  ExprVector foo1_types = {bind::rangeTy(bind::fname(map_var)), iTy, iTy, bTy};
  // reused for foo2 & foo3

  Expr foo1_decl = mkFun("foo1", foo1_types);
  ExprVector foo1_app_args = {map_var, k1, v};
  Expr foo1_app = bind::fapp(foo1_decl, foo1_app_args);
  // cl1 foo1(map, k1, v) :- v = get(map, k1).
  Expr cl1 = boolop::limp(get_map, foo1_app);

  Expr bar_decl = mkFun("bar", {bind::rangeTy(bind::fname(map_var)), bTy});

  Expr foo2_decl = mkFun("foo2", foo1_types);
  Expr foo2_app = bind::fapp(foo2_decl, foo1_app_args);
  // cl2 foo2(map, k1, v) :- v = get(map, k1), bar(map).
  Expr cl2 =
      boolop::limp(mk<AND>(get_map, bind::fapp(bar_decl, map_var)), foo2_app);

  Expr mapA_var = mkFMapConstInt("mapA", keys);
  Expr get_mapA = finite_map::get(mapA_var, k1);
  Expr set = finite_map::set(mapA_var, k1, mk<PLUS>(get_mapA, mkInt(1, efac)));
  Expr foo3_decl = mkFun("foo3", foo1_types);
  Expr foo3_app = bind::fapp(foo3_decl, foo1_app_args); // reusing foo1_args
  // cl3: foo(map, k1, x) :- map = set(mapA, k1, +(get(mapA, k1), 1)),
  //                         bar(mapA).
  Expr cl3 = boolop::limp(
      mk<AND>(mk<EQ>(map_var, set), bind::fapp(bar_decl, mapA_var)), foo3_app);

  db.registerRelation(foo1_decl);
  db.registerRelation(foo2_decl);
  db.registerRelation(foo3_decl);
  db.registerRelation(bar_decl);

  ExprSet rule_vars(foo1_app_args.begin(), foo1_app_args.end());

  for (auto k_it : keys) {
    Expr var = k_it;
    rule_vars.insert(var);
  }

  db.addRule(rule_vars, cl1);
  db.addRule(rule_vars, cl2); // same vars as foo1
  rule_vars.insert(mapA_var);
  db.addRule(rule_vars, cl3);

  // query
  Expr solution = mkInt(42, efac);
  Expr mapVar = mkFMapConstInt("m", keys);
  ExprVector values = {solution};
  auto k_it = ++keys.begin();

  Expr zero = mkInt(0, efac);
  // initialize the rest of the map with 0
  while (k_it != keys.end()) {
    values.push_back(zero);
    k_it++;
  }

  ExprVector qargs = {mapVar, keys[0], v};
  ExprVector qBody = {mk<EQ>(mapVar, finite_map::constFiniteMap(keys, values)),
                      bind::fapp(foo2_decl, qargs), mk<NEQ>(v, solution)};

  ExprSet vars(qargs.begin(), qargs.end());
  for (auto it : keys)
    vars.insert(it);

  return registerQueryHornClauseDB(mknary<AND>(qBody), vars, db);
}

TEST_CASE("expr.finite_map.full_transf_1key") {

  ExprFactory efac;
  HornClauseDB db(efac);

  ExprVector keys = {mkIntKey(1, efac)};

  Expr query = test_rules_map_args(db, keys);

  errs() << "HornClauseDB with fmaps in args\n";
  errs() << db << "\n";

  HornClauseDB tdb(efac);
  removeFiniteMapsHornClausesTransf(db, tdb);

  errs() << "HornClauseDB without fmaps\n";
  errs() << tdb << "\n";
  // original query:
  // query :- m = defmap(defmap(defk(k1), fmap-default(0)), defv(42)),
  //          foo1(m, k1, v), v \= 42.
  // UNSAT

  CHECK(!solveHornClauseDBZ3(tdb));
}

TEST_CASE("expr.finite_map.full_transf_2keys") {

  ExprFactory efac;
  HornClauseDB db(efac);
  ExprVector keys = {mkIntKey(1, efac), mkIntKey(2, efac)};

  Expr query = test_rules_map_args(db, keys);

  query->dump(); // ensure dump in the executable for debugging
  errs() << "HornClauseDB with fmaps  -------------------- \n";
  errs() << db << "\n";
  // This cannot be solved by Z3

  HornClauseDB tdb(efac);
  removeFiniteMapsHornClausesTransf(db, tdb);

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
  errs() << tdb << "\n";
  // This should be solvable by Z3

  CHECK(!solveHornClauseDBZ3(tdb));
}
