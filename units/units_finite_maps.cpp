#include "doctest.h"
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "llvm/Support/raw_ostream.h"

using namespace std;
using namespace expr;
using namespace expr::op;
using namespace seahorn;

TEST_CASE("expr.finite_map.create_map") {

  ExprFactory efac;
  ExprVector keys;

  Expr key1 = bv::bvConst(mkTerm<std::string>("k1", efac), 32);

  keys.push_back(key1);
  Expr map = finite_map::constFiniteMap(keys);

  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) == "defk(k1)");

  errs() << *map << "\n";
}

TEST_CASE("expr.finite_map.set") {

  ExprFactory efac;
  ExprVector keys;

  Expr key1 = bv::bvConst(mkTerm<std::string>("k1", efac), 32);

  keys.push_back(key1);
  Expr map = finite_map::constFiniteMap(keys);

  unsigned value = 30;
  Expr v = mkTerm<expr::mpz_class>(value, efac);
  Expr map1 = finite_map::set(map, finite_map::constFiniteMap(keys),  key1, v);

  CHECK(map1);
  CHECK(boost::lexical_cast<std::string>(*map1) ==
        "set(defk(k1), k1, 30)");

  errs() << *map1 << "\n";
}

TEST_CASE("expr.finite_map.get") {
  using namespace expr;
  using namespace expr::op;

  ExprFactory efac;
  ExprVector keys;

  Expr key1 = bv::bvConst(mkTerm<std::string>("k1", efac), 32);

  keys.push_back(key1);
  Expr map = finite_map::constFiniteMap(keys);

  Expr eget = finite_map::get(map, finite_map::constFiniteMap(keys), key1);

  CHECK(eget);
  CHECK(boost::lexical_cast<std::string>(*eget) == "get(defk(k1), k1)");

  errs() << *eget << "\n";
}

TEST_CASE("expr.finite_map.create_set_3") {

  ExprFactory efac;
  ExprVector keys;

  Expr key1 = bv::bvConst(mkTerm<std::string>("k1", efac), 32);
  Expr key2 = bv::bvConst(mkTerm<std::string>("k2", efac), 32);
  Expr key3 = bv::bvConst(mkTerm<std::string>("k3", efac), 32);

  keys.push_back(key1);
  keys.push_back(key2);
  keys.push_back(key3);

  Expr map, map_keys = finite_map::constFiniteMap(keys);
  map = map_keys;

  Expr v = mkTerm<expr::mpz_class>(31, efac);
  map = finite_map::set(map, map_keys, key1, v);

  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "set(defk(k1, k2, k3), k1, 31)");

  errs() << *map << "\n";

  v = mkTerm<expr::mpz_class>(32, efac);
  map = finite_map::set(map, map_keys, key2, v);
  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "set(set(defk(k1, k2, k3), k1, 31), k2, 32)");

  errs() << *map << "\n";

  v = mkTerm<expr::mpz_class>(33, efac);
  map = finite_map::set(map, map_keys, key3, v);
  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "set(set(set(defk(k1, k2, k3), k1, 31), k2, 32), k3, 33)");

  errs() << *map << "\n";
}

TEST_CASE("expr.finite_map.create_keys_lambda") {

  ExprFactory efac;

  Expr x = bind::intConst(mkTerm<string>("x", efac));

  ExprVector keys;

  keys.push_back(bind::intConst(mkTerm<string>("k1", efac)));

  Expr lambda_keys = finite_map::make_lambda_map_keys(keys, efac);
  CHECK(boost::lexical_cast<std::string>(lambda_keys) ==
        "(lambda (INT) ite(k1=(B0:INT), 1, 0))");

  errs() << "lambda_keys of def(k1): " << *lambda_keys << "\n";

  keys.push_back(bind::intConst(mkTerm<std::string>("k2", efac)));
  lambda_keys = finite_map::make_lambda_map_keys(keys, efac);

  CHECK(boost::lexical_cast<std::string>(lambda_keys) ==
        "(lambda (INT) ite(k2=(B0:INT), 2, ite(k1=(B0:INT), 1, 0)))");

  errs() << "lambda_keys of def(k1, k2): " << *lambda_keys << "\n";

  keys.push_back(bind::intConst(mkTerm<std::string>("k3", efac)));
  lambda_keys = finite_map::make_lambda_map_keys(keys, efac);

  CHECK(boost::lexical_cast<std::string>(lambda_keys) ==
        "(lambda (INT) ite(k3=(B0:INT), 3, ite(k2=(B0:INT), 2, "
        "ite(k1=(B0:INT), 1, 0))))");
  errs() << "lambda_keys of def(k1, k2, k3)): " << *lambda_keys << "\n";
}

TEST_CASE("expr.finite_map.set_map_lambda") {

  ExprFactory efac;

  ExprVector keys;

  Expr k1 = bind::intConst(mkTerm<std::string>("k1", efac));
  keys.push_back(k1);
  keys.push_back(bind::intConst(mkTerm<std::string>("k2", efac)));
  keys.push_back(bind::intConst(mkTerm<std::string>("k3", efac)));

  Expr lambda_keys = finite_map::make_lambda_map_keys(keys, efac);
  CHECK(boost::lexical_cast<std::string>(lambda_keys) ==
        "(lambda (INT) ite(k3=(B0:INT), 3, ite(k2=(B0:INT), 2, "
        "ite(k1=(B0:INT), 1, 0))))");

  Expr value = mkTerm<expr::mpz_class>(42, efac);

  Expr map = finite_map::new_map_lambda(efac);
  // set the value of k1
  map = finite_map::set_map_lambda(map, lambda_keys, k1, value, efac);

  CHECK(boost::lexical_cast<std::string>(map) ==
        "(lambda (INT) ite((B0:INT)=ite(k3=k1, 3, ite(k2=k1, 2, ite(k1=k1, 1, "
        "0))), 42, 0))");

  errs() << "set(new_map, defk(k1,k2,k3),k1,42): " << *map << "\n";

  EZ3 z3(efac);

  errs() << *z3_simplify(z3, map) << "\n";
}

TEST_CASE("expr.finite_map.get_after_set_map_lambda") {
  using namespace std;
  using namespace expr;
  using namespace expr::op;
  using namespace seahorn;

  ExprFactory efac;

  ExprVector keys;

  Expr k1 = bind::intConst(mkTerm<std::string>("k1", efac));
  keys.push_back(k1);
  keys.push_back(bind::intConst(mkTerm<std::string>("k2", efac)));
  keys.push_back(bind::intConst(mkTerm<std::string>("k3", efac)));

  Expr lambda_keys = finite_map::make_lambda_map_keys(keys, efac);
  CHECK(boost::lexical_cast<std::string>(lambda_keys) ==
        "(lambda (INT) ite(k3=(B0:INT), 3, ite(k2=(B0:INT), 2, "
        "ite(k1=(B0:INT), 1, 0))))");

  Expr value = mkTerm<expr::mpz_class>(42, efac);

  Expr map = finite_map::new_map_lambda(efac); // init map
  map = finite_map::set_map_lambda(map, lambda_keys, k1, value, efac);

  CHECK(boost::lexical_cast<std::string>(map) ==
        "(lambda (INT) ite((B0:INT)=ite(k3=k1, 3, ite(k2=k1, 2, ite(k1=k1, 1, "
        "0))), 42, 0))");

  Expr get_value = finite_map::get_map_lambda(map, lambda_keys, k1);

  CHECK(boost::lexical_cast<std::string>(get_value) ==
        "ite(ite(k3=k1, 3, ite(k2=k1, 2, ite(k1=k1, 1, 0)))=ite(k3=k1, 3, "
        "ite(k2=k1, 2, ite(k1=k1, 1, 0))), 42, 0)");

  EZ3 z3(efac);

  errs() << "get(set(defk(k1,k2,k3),k1,42), k1): "
         << *map << "\n";

  errs() << *z3_simplify(z3, get_value) << "\n";

  // replace by expression to check satisfiability
  //
  CHECK(boost::lexical_cast<std::string>(z3_simplify(
            z3, mk<EQ>(get_value, mkTerm<expr::mpz_class>(42, efac)))) ==
        "true");
}

TEST_CASE("expr.finite_map.make_map_batch_values") {

  using namespace std;
  using namespace expr;
  using namespace expr::op;
  using namespace seahorn;

  ExprFactory efac;
  ExprVector keys;

  Expr k1 = bind::intConst(mkTerm<std::string>("k1", efac));
  Expr k2 = bind::intConst(mkTerm<std::string>("k2", efac));
  Expr k3 = bind::intConst(mkTerm<std::string>("k3", efac));

  keys.push_back(k1);
  keys.push_back(k2);
  keys.push_back(k3);

  ExprVector values;

  values.push_back(mkTerm<expr::mpz_class>(41, efac));
  values.push_back(mkTerm<expr::mpz_class>(42, efac));
  values.push_back(mkTerm<expr::mpz_class>(43, efac));

  Expr lmd_keys, lmd_values;

  lmd_values = finite_map::make_map_batch_values(keys, values, efac, lmd_keys);

  errs() << "\n----------\nkeys:   " << *lmd_keys << "\n";
  errs() << "values: " << *lmd_values << "\n";

  EZ3 z3(efac);

  // uninterpreted map
  Expr u_map = finite_map::constFiniteMap(keys);

  int count = 41;
  for (auto k : keys) {
    u_map = finite_map::set(u_map, u_map, k1, mkTerm<expr::mpz_class>(count++, efac));
    count++;
  }

  errs() << "map:    " << *u_map << "\n\n";

  for (int i = 0; i < keys.size(); i++) {
    Expr get_value = finite_map::get_map_lambda(lmd_values, lmd_keys, keys[i]);
    Expr to_simp_true = mk<EQ>(get_value, values[i]);
    // cannot be simplified if constructed in a batch
    errs() << "simplifying: "
           << *mk<EQ>(finite_map::get(u_map, u_map,keys[i]), values[i])
           << "\n";
    errs() << "orig:        " << *to_simp_true << "\n";
    errs() << "simplified:  " << *z3_simplify(z3, to_simp_true) << "\n\n";

    // CHECK(boost::lexical_cast<std::string>(z3_simplify(z3, to_simp_true)) ==
    //       "true");
  }
}

TEST_CASE("expr.finite_map.make_map_sequence_gets") {

  ExprFactory efac;
  ExprVector keys;

  Expr k1 = bind::intConst(mkTerm<std::string>("k1", efac));
  Expr k2 = bind::intConst(mkTerm<std::string>("k2", efac));
  Expr k3 = bind::intConst(mkTerm<std::string>("k3", efac));

  keys.push_back(k1);
  keys.push_back(k2);
  keys.push_back(k3);

  ExprVector values;

  values.push_back(mkTerm<expr::mpz_class>(41, efac));
  values.push_back(mkTerm<expr::mpz_class>(42, efac));
  values.push_back(mkTerm<expr::mpz_class>(43, efac));

  Expr lmd_keys, lmd_values;

  lmd_values = finite_map::make_map_sequence_gets(keys, values, efac, lmd_keys);

  errs() << "\n\n----------\nkeys:   " << *lmd_keys << "\n";
  errs() << "values: " << *lmd_values << "\n";

  EZ3 z3(efac);

  // uninterpreted map
  Expr u_map = finite_map::constFiniteMap(keys);
  Expr u_map_keys = u_map;
  int count = 41;
  for ( auto k : keys) {
    u_map = finite_map::set(u_map, u_map_keys, k1,
                            mkTerm<expr::mpz_class>(count, efac));
    count++;
  }

  errs() << "map:    " << *u_map << "\n\n";

  for(int i = 0; i < keys.size(); i++) {
    Expr get_value = finite_map::get_map_lambda(lmd_values, lmd_keys, keys[i]);
    Expr to_simp_true = mk<EQ>(get_value, values[i]);
    // cannot be simplified if nothing is known about the keys (they may alias)
    errs() << "simplifying: "
           << *mk<EQ>(finite_map::get(u_map, u_map_keys, keys[i]), values[i])
           << "\n";
    errs() << "orig:        " << *to_simp_true << "\n";
    errs() << "simplified:  " << *z3_simplify(z3, to_simp_true) << "\n\n";

    // CHECK(boost::lexical_cast<std::string>(z3_simplify(z3, to_simp_true)) ==
    //       "true");
  }
}

bool register_rule_and_query(Expr query, ExprVector &qvars, ExprFactory &efac,
                             ZFixedPoint<EZ3> &fp) {
  ExprVector qtype;
  qtype.push_back(mk<BOOL_TY>(efac)); // at least return argument required
  Expr query_name = mkTerm<string>("query1", efac);

  Expr qdecl = bind::fdecl(query_name, qtype);
  fp.registerRelation(qdecl);

  fp.addRule(qvars, boolop::limp(query, bind::fapp(qdecl)));

  Expr q = bind::fapp(qdecl);
  errs() << fp.toString(q) << "\n";
  boost::tribool res = fp.query(q);
  errs() << "Solving: " << (res ? "sat" : "unsat") << "\n";
  return static_cast<bool>(res);
}

void set_params(EZ3 &z3, ZFixedPoint<EZ3> &fp) {

  ZParams<EZ3> params(z3); // see HornSolver.cc for more default values
  params.set(":engine", "spacer");
  params.set(":xform.slice", false);
  params.set(":xform.inline-linear", false);
  params.set(":xform.inline-eager", false);

  fp.set(params);
}

// checking maps in the body of a rule
TEST_CASE("expr.finite_map.map_in_body_1key") {

  ExprFactory efac;
  Expr k1 = bind::intConst(mkTerm<string>("k1", efac));
  Expr v1 = bind::intConst(mkTerm<string>("v1", efac));
  Expr x = bind::intConst(mkTerm<string>("x", efac));

  Expr iTy = mk<INT_TY>(efac);
  Expr bTy = mk<BOOL_TY>(efac);

  ExprVector ftype;
  ftype.push_back(iTy);
  ftype.push_back(bTy); // return type?

  Expr fdecl = bind::fdecl(mkTerm<string>("f", efac), ftype);
  Expr fapp = bind::fapp(fdecl,x);

  EZ3 z3(efac);
  ZFixedPoint<EZ3> fp(z3);
  ZParams<EZ3> params(z3);  // TODO: see HornSolver.cc for more default values
  params.set(":engine", "spacer");
  params.set(":xform.slice", false);
  params.set(":xform.inline-linear", true);
  params.set(":xform.inline-eager", true);

  Expr solution = mkTerm<expr::mpz_class>(42, efac);

  ExprVector keys, values;
  keys.push_back(bind::intConst(k1));
  values.push_back(mkTerm<expr::mpz_class>(1UL, efac));

  Expr unint = finite_map::constFiniteMap(keys);
  Expr unint_ops = mk<EQ>(
      x, finite_map::get(
             finite_map::set(finite_map::set(unint, unint, keys[0], values[0]),
                             unint, keys[0], solution),
             unint, keys[0]));

  ExprVector vars;
  vars.push_back(v1);
  vars.push_back(k1);
  vars.push_back(x);

  ExprVector body;
  body.push_back(mk<EQ>(v1, mkTerm<expr::mpz_class>(1UL, efac)));
  Expr map_keys;
  Expr map = finite_map::make_map_batch_values(keys,values,efac,map_keys);
  Expr setop = finite_map::set_map_lambda(map, map_keys, k1, solution, efac);
  Expr getop = finite_map::get_map_lambda(setop, map_keys, k1);
  body.push_back(mk<EQ>(x, getop));

  fp.set(params);
  fp.registerRelation(fdecl);
  fp.addRule(vars, boolop::limp(mknary<AND>(body), fapp));

  ExprVector qvars;
  Expr query;

  qvars.push_back(x);
  query = mk<AND>(mk<NEQ>(x, solution), bind::fapp(fdecl, x));

  errs() << "Expected: unsat\n";
  CHECK(!register_rule_and_query(query, qvars, efac, fp));

  // example with map operations in 1 literal:
  // f(x) :-
  //    v1=1,
  //    x = get(set(mkmap((k1),(v1)),k1, 42)).
  // query :- x /= 42, f(x).
  // UNSAT
}

TEST_CASE("expr.finite_map.map_in_body_2keys") {

  ExprFactory efac;
  Expr k1 = bind::intConst(mkTerm<string>("k1", efac));
  Expr k2 = bind::intConst(mkTerm<string>("k2", efac));
  Expr v1 = bind::intConst(mkTerm<string>("v1", efac));
  Expr v2 = bind::intConst(mkTerm<string>("v2", efac));
  Expr x = bind::intConst(mkTerm<string>("x", efac));
  Expr y = bind::intConst(mkTerm<string>("y", efac));

  Expr iTy = mk<INT_TY>(efac);
  Expr bTy = mk<BOOL_TY>(efac);

  ExprVector ftype;
  ftype.push_back(iTy);
  ftype.push_back(iTy);
  ftype.push_back(iTy);
  ftype.push_back(iTy);
  ftype.push_back(bTy);

  ExprVector args;
  args.push_back(k1);
  args.push_back(k2);
  args.push_back(x);
  args.push_back(y);

  Expr fdecl = bind::fdecl(mkTerm<string>("f", efac), ftype);
  Expr fapp = bind::fapp(fdecl,args);

  EZ3 z3(efac);
  ZFixedPoint<EZ3> fp(z3);
  set_params(z3, fp);

  ExprVector keys, values;
  keys.push_back(k1);
  keys.push_back(k2);

  values.push_back(mkTerm<expr::mpz_class>(1, efac));
  values.push_back(mkTerm<expr::mpz_class>(2, efac));

  Expr unint = finite_map::constFiniteMap(keys);
  Expr unint_map = finite_map::set(
      finite_map::set(finite_map::set(unint, unint, keys[0], values[0]), unint,
                      keys[1], values[1]),
      unint, keys[0], mkTerm<expr::mpz_class>(42, efac));

  ExprVector unint_ops;
  unint_ops.push_back(mk<EQ>(x, finite_map::get(unint_map, unint, keys[0])));
  unint_ops.push_back(mk<EQ>(y, finite_map::get(unint_map, unint, keys[1])));

  ExprVector vars;
  vars.push_back(v1);
  vars.push_back(v2);
  vars.push_back(k1);
  vars.push_back(k2);
  vars.push_back(x);
  vars.push_back(y);

  ExprVector body;
  body.push_back(mk<EQ>(v1, values[0]));
  Expr sol = mkTerm<expr::mpz_class>(42, efac);

  Expr map_keys;
  Expr map = z3_simplify(z3, finite_map::make_map_batch_values(keys,values,efac,map_keys));
  Expr setop =
    z3_simplify(z3, finite_map::set_map_lambda(map, map_keys, k1, sol, efac));
  body.push_back(mk<EQ>(x, z3_simplify(z3,finite_map::get_map_lambda(setop, map_keys, k1))));
  body.push_back(mk<EQ>(y, z3_simplify(z3,finite_map::get_map_lambda(setop, map_keys, k2))));

  fp.registerRelation(fdecl);
  fp.addRule(vars, boolop::limp(mknary<AND>(body), fapp));

  ExprVector query_args;

  query_args.push_back(k1);
  query_args.push_back(k2);
  query_args.push_back(x);
  query_args.push_back(y);

  boost::tribool res;
  ExprVector query;

  ExprVector qvars;
  qvars.push_back(k1);
  qvars.push_back(k2);
  qvars.push_back(x);
  qvars.push_back(y);

  // example with map operations in 1 literal:
  // f(k1,k2,x,y) :-
  //    v1=1, v2=2,
  //    x = get(set(mkmap((k1,k2),(v1,v2)),k1, 42)),
  //    y = get(set(mkmap((k1,k2),(v1,v2)),k2, 42)).

  #define ALIAS
#ifdef ALIAS
  errs() << "\n----------------------------\nwith aliasing:\n";
  query.push_back(mk<EQ>(k1, k2));
  query.push_back(mk<OR>(mk<NEQ>(x, sol), mk<NEQ>(y, sol)));
  query.push_back(bind::fapp(fdecl, query_args));
  // query1 :- k1=k2, or(x\=42, y\=42), f(k1, k2, 42, 42). // aliasing
  // UNSAT
#else
  errs() << "\n----------------------------\nwith no aliasing:\n";
  query.push_back(boolop::limp(mk<NEQ>(k1, k2), mk<AND>(mk<OR>(mk<NEQ>(x, sol), mk<NEQ>(y, values[1])), bind::fapp(fdecl, query_args))));
  // query2 :- k1\=k2, or(x\=42, y\=2), f(k1, k2, 42, 2). // no aliasing
  // UNSAT
#endif

  // this check is not working with no alias (the output is sat)
  errs() << "Expected: unsat\n";
  CHECK(!register_rule_and_query(mknary<AND>(query), qvars, efac, fp));
}

TEST_CASE("expr.finite_map.caller_callsite") {

  ExprFactory efac;
  Expr in_map, map_keys, out_map;
  ExprVector keys_used, new_params;

  ExprVector in_values;

  Expr key_base = mkTerm<string>("k", efac);
  int count = 1;

#define MAX_K 2

  for(int i = 0 ; i < MAX_K ; i++){
    keys_used.push_back(
                      bind::intConst(variant::variant(count, key_base)));
    in_values.push_back(mkTerm<expr::mpz_class>(count + 40, efac));
    count++;
  }

  in_map = finite_map::make_map_batch_values(keys_used, in_values, efac, map_keys);

  errs() << "Map in: " << *in_map << "\n";
  errs() << "Map keys: " << *map_keys << "\n";

  Expr extra_lits = finite_map::prepare_finite_maps_caller_callsite(
      in_map, map_keys, keys_used, efac, new_params, out_map);

  EZ3 z3(efac);
  errs() << "Extra literals: " << *z3_simplify(z3, extra_lits) << "\n";
  errs() << "New params:\n";
  for (auto e : new_params){
    errs() << "\t" << *e << "\n";
  }
  errs() << "Out map lambda: " << *z3_simplify(z3, out_map) << "\n";
}

#ifdef BUGS
TEST_CASE("expr.finite_map.duplicated_and_query" * doctest::skip(true)) {

  using namespace std;
  using namespace expr;
  using namespace expr::op;
  using namespace seahorn;

  ExprFactory efac;
  Expr k1 = bind::intConst(mkTerm<string>("k1", efac));
  Expr k2 = bind::intConst(mkTerm<string>("k2", efac));
  Expr v1 = bind::intConst(mkTerm<string>("v1", efac));
  Expr v2 = bind::intConst(mkTerm<string>("v2", efac));
  Expr x = bind::intConst(mkTerm<string>("x", efac));
  Expr y = bind::intConst(mkTerm<string>("y", efac));

  Expr iTy = mk<INT_TY>(efac);
  Expr bTy = mk<BOOL_TY>(efac);

  ExprVector ftype;
  ftype.push_back(iTy);
  ftype.push_back(iTy);
  ftype.push_back(iTy);
  ftype.push_back(iTy);
  ftype.push_back(bTy);

  ExprVector args;
  args.push_back(k1);
  args.push_back(k2);
  args.push_back(x);
  args.push_back(y);

  Expr fdecl = bind::fdecl(mkTerm<string>("f", efac), ftype);
  Expr fapp = bind::fapp(fdecl,args);

  EZ3 z3(efac);
  ZFixedPoint<EZ3> fp(z3);
  ZParams<EZ3> params(z3);
  params.set(":engine", "spacer");
  params.set(":xform.slice", false);
  params.set(":xform.inline-linear", false);
  params.set(":xform.inline-eager", false);

  ExprVector keys, values;
  keys.push_back(k1);
  keys.push_back(k2);

  values.push_back(mkTerm<expr::mpz_class>(1UL, efac));
  values.push_back(mkTerm<expr::mpz_class>(2UL, efac));

  Expr unint = finite_map::constFiniteMap(keys);
  Expr unint_map = finite_map::set(
      finite_map::set(finite_map::set(unint, unint, keys[0], values[0]), unint,
                      keys[1], values[1]),
      unint, keys[0], mkTerm<expr::mpz_class>(42, efac));

  ExprVector unint_ops;
  unint_ops.push_back(mk<EQ>(x, finite_map::get(unint_map, unint, keys[0])));
  unint_ops.push_back(mk<EQ>(y, finite_map::get(unint_map, unint, keys[1])));

  ExprVector vars;
  vars.push_back(v1);
  vars.push_back(v2);
  vars.push_back(k1);
  vars.push_back(k2);
  vars.push_back(x);
  vars.push_back(y);

  ExprVector body;
  body.push_back(mk<EQ>(v1, mkTerm<expr::mpz_class>(1UL, efac)));
  Expr map_keys;
  Expr map = finite_map::make_map_batch_values(keys,values,efac,map_keys);
  Expr setop = finite_map::set_map_lambda(map, map_keys, k1, mkTerm<expr::mpz_class>(42, efac), efac);
  body.push_back(mk<EQ>(x, z3_simplify(z3,finite_map::get_map_lambda(setop, map_keys, k1))));
  body.push_back(mk<EQ>(y, z3_simplify(z3,finite_map::get_map_lambda(setop, map_keys, k2))));

  fp.set(params);
  fp.registerRelation(fdecl);
  fp.addRule(vars, boolop::limp(mknary<AND>(body), fapp));

  ExprVector query_args;
  Expr sol = mkTerm<expr::mpz_class>(42, efac);

  query_args.push_back(k1);
  query_args.push_back(k2);
  query_args.push_back(x);
  query_args.push_back(y);

  boost::tribool res;
  ExprVector query;

  errs() << "\n----------------------------\nwith aliasing:\n";
  query.push_back(mk<EQ>(k1, k2));
  // query.push_back(mk<NEQ>(x, sol));
  query.push_back(mk<NEQ>(y, sol));
  query.push_back(bind::fapp(fdecl, query_args));
  Expr qa = mknary<AND>(query);
  errs() << fp.toString(qa) << "\n";
  res = fp.query(qa);
  errs() << "Solving: " << (res ? "sat" : "unsat") << "\n";
  CHECK(!static_cast<bool>(res));

  errs() << "\n----------------------------\nwith no aliasing:\n";
  query.clear();
  query.push_back(mk<NEQ>(k1, k2));
  query.push_back(mk<OR>(mk<NEQ>(x, sol), mk<NEQ>(y, values[1])));
  query.push_back(bind::fapp(fdecl, query_args));
  Expr qna =  mknary<AND>(query);
  errs() << fp.toString(qna) << "\n";
  res = fp.query(qna);
  errs() << "Solving: " << (res ? "sat" : "unsat") << "\n";
  // CHECK(!static_cast<bool>(res));
}

TEST_CASE("expr.finite_map.param_exception" * doctest::skip(true)) {

  using namespace std;
  using namespace expr;
  using namespace expr::op;
  using namespace seahorn;

  ExprFactory efac;

  EZ3 z3(efac);
  ZFixedPoint<EZ3> fp(z3);
  ZParams<EZ3> params(z3);
  params.set(":engine", "spacer");
  params.set(":pdr.farkas", true);

  fp.set(params);
}

// checking maps in the body of a rule
TEST_CASE("expr.finite_map.query_exists") {

  using namespace std;
  using namespace expr;
  using namespace expr::op;
  using namespace seahorn;

  ExprFactory efac;
  Expr k1 = bind::intConst(mkTerm<string>("k1", efac));
  Expr v1 = bind::intConst(mkTerm<string>("v1", efac));
  Expr x = bind::intConst(mkTerm<string>("x", efac));

  Expr iTy = mk<INT_TY>(efac);
  Expr bTy = mk<BOOL_TY>(efac);

  ExprVector ftype;
  ftype.push_back(iTy);
  ftype.push_back(bTy); // return type?

  Expr fdecl = bind::fdecl(mkTerm<string>("f", efac), ftype);
  Expr fapp = bind::fapp(fdecl,x);

  EZ3 z3(efac);
  ZFixedPoint<EZ3> fp(z3);
  ZParams<EZ3> params(z3);  // TODO: see HornSolver.cc for more default values
  params.set(":engine", "spacer");
  params.set(":xform.slice", false);
  params.set(":xform.inline-linear", false);
  params.set(":xform.inline-eager", false);


  Expr solution = mkTerm<expr::mpz_class>(42, efac);

  ExprVector keys, values;
  keys.push_back(bind::intConst(mkTerm<std::string>("k1", efac)));
  values.push_back(mkTerm<expr::mpz_class>(1UL, efac));

  Expr unint = finite_map::constFiniteMap(keys);
  Expr unint_ops = mk<EQ>(
      x, finite_map::get(
             finite_map::set(finite_map::set(unint, unint, keys[0], values[0]),
                             unint, keys[0], solution),
             unint, keys[0]));

  ExprVector vars;
  vars.push_back(v1);
  vars.push_back(k1);
  vars.push_back(x);

  ExprVector body;
  body.push_back(mk<EQ>(v1, mkTerm<expr::mpz_class>(1UL, efac)));
  Expr map_keys;
  Expr map = finite_map::make_map_batch_values(keys,values,efac,map_keys);
  Expr setop = finite_map::set_map_lambda(map, map_keys, k1, solution, efac);
  Expr getop = finite_map::get_map_lambda(setop, map_keys, k1);
  body.push_back(mk<EQ>(x, getop));

  fp.set(params);
  fp.registerRelation(fdecl);
  fp.addRule(vars, boolop::limp(mknary<AND>(body), fapp));

  Expr q = bind::fapp(fdecl, x);

  boost::tribool res;
  ExprVector query;

  Expr qa = mk<AND>(mk<NEQ>(x, solution), bind::fapp(fdecl, x));
  errs() << "\n----------------------------\none key:\n";
  errs() << fp.toString(qa) << "\n";
  res = fp.query(qa);
  errs() << "Solving: " << (res ? "sat" : "unsat") << "\n";
  CHECK(!static_cast<bool>(res));

  // example with map operations in 1 literal:
  // main1(x) :-
  //    v1=1,
  //    x = get(set(mkmap((k1),(v1)),k1, 42)).
  // query :- x /= 42, main1(x).
  // UNSAT
}
#endif

TEST_CASE("expr.finite_map.simple_query" * doctest::skip(true)) {

  using namespace std;
  using namespace expr;
  using namespace expr::op;
  using namespace seahorn;

  //  errs() << "begin test\n";
  ExprFactory efac;

  EZ3 z3(efac);
  ZFixedPoint<EZ3> fp(z3);

  set_params(z3, fp);

  Expr solution = mkTerm<expr::mpz_class>(42, efac);

  // add a rule for the query
  ExprVector qtype, qvars;
  Expr bTy = mk<BOOL_TY>(efac);
  qtype.push_back(bTy); // at least the return argument is required

  Expr query_name = mkTerm<std::string>("query1", efac);

  Expr x = bind::intConst(mkTerm<string>("x", efac));
  qvars.push_back(x);

  Expr qdecl = bind::fdecl(query_name, qtype);
  fp.registerRelation(qdecl);

  Expr q_body = mk<NEQ>(x, solution);
  errs() << "q_body: " << *q_body << "\n";
  errs() << "q_rule: " << *boolop::limp(q_body, bind::fapp(qdecl)) << "\n";
  fp.addRule(qvars, boolop::limp(q_body, bind::fapp(qdecl)));
  // query1 :- x /= 42.

  Expr q = bind::fapp(qdecl);
  errs() << "query: " << *q << "\nfp content:\n";
  errs() << fp.toString(q) << "\nend fp content\n";
  boost::tribool res = fp.query(q);
  errs() << "Solving: " << (res ? "sat" : "unsat") << "\n";
  CHECK(static_cast<bool>(res));
  // SAT
}


