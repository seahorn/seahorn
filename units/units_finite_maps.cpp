#include "doctest.h"
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "llvm/Support/raw_ostream.h"

TEST_CASE("expr.finite_map.create_map") {
  using namespace expr;
  using namespace expr::op;

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
  using namespace expr;
  using namespace expr::op;

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
  using namespace expr;
  using namespace expr::op;

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
  using namespace std;
  using namespace expr;
  using namespace expr::op;
  using namespace seahorn;

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


// checking maps in the body of a rule
TEST_CASE("expr.finite_map.map_in_body_1key") {

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

  // example with map operations in 1 literal:
  // main1(x) :-
  //    v1=1,
  //    x = get(set(mkmap((k1),(v1)),k1, 42)).
  // query :- main1(42).
  // SAT

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

  // same example as above with more than one literal:
  // main1(x) :-
  //    v1=1,
  //    map = mkmap((k1),(v1)),
  //    map2 = set(map,(k1), k1, 42),
  //    x = get(map2,k1).
  // query :- main1(42).
  // SAT
}

TEST_CASE("expr.finite_map.map_in_body_2keys") {

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
  ZParams<EZ3> params(z3);  // TODO: see HornSolver.cc for more default values
  params.set(":engine", "spacer");
  params.set(":xform.slice", false);
  params.set(":xform.inline-linear", false);
  params.set(":xform.inline-eager", false);

  // example with map operations in 1 literal:
  // main1(x,y) :-
  //    v1=1, v2=2,
  //    map = set(mkmap((k1,k2),(v1,v2)),k1, 42),
  //    x = get(set(mkmap((k1,k2),(v1,v2)),k1, 42)),
  //    y = get(set(mkmap((k1,k2),(v1,v2)),k2, 42)).
  // query1 :- k1 = k2, main1(k1, k2, 42, 42).
  // query2 :- k1 > k2, main1(k1, k2, 42, 2).
  // SAT

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
  query.push_back(mk<NEQ>(x, sol));
  query.push_back(mk<NEQ>(y, values[1]));
  query.push_back(bind::fapp(fdecl, query_args));
  Expr qa = mknary<AND>(query);
  errs() << fp.toString(qa) << "\n";
  res = fp.query(qa);
  errs() << "Solving: " << (res ? "sat" : "unsat") << "\n";
  CHECK(!static_cast<bool>(res));

  errs() << "\n----------------------------\nwith no aliasing:\n";
  query.clear();
  query.push_back(mk<NEQ>(k1, k2));
  query.push_back(mk<NEQ>(x, sol));
  query.push_back(mk<NEQ>(y, values[1]));
  query.push_back(bind::fapp(fdecl, query_args));
  Expr qna =  mknary<AND>(query);
  errs() << fp.toString(qna) << "\n";
  res = fp.query(qna);
  errs() << "Solving: " << (res ? "sat" : "unsat") << "\n";
  CHECK(!static_cast<bool>(res));

}
