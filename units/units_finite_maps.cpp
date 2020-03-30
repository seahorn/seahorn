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
  Expr map1 = finite_map::set(map, key1, v);

  CHECK(map1);
  CHECK(boost::lexical_cast<std::string>(*map1) == "set(defk(k1), k1, 30)");
}

TEST_CASE("expr.finite_map.get") {
  using namespace expr;
  using namespace expr::op;

  ExprFactory efac;
  ExprVector keys;

  Expr key1 = bv::bvConst(mkTerm<std::string>("k1", efac), 32);

  keys.push_back(key1);
  Expr map = finite_map::constFiniteMap(keys);

  Expr eget = finite_map::get(map, key1);

  CHECK(eget);
  CHECK(boost::lexical_cast<std::string>(*eget) == "get(defk(k1), k1)");
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

  Expr map = finite_map::constFiniteMap(keys);

  Expr v = mkTerm<expr::mpz_class>(31, efac);
  map = finite_map::set(map, key1, v);

  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "set(defk(k1, k2, k3), k1, 31)");

  v = mkTerm<expr::mpz_class>(32, efac);
  map = finite_map::set(map, key2, v);
  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "set(set(defk(k1, k2, k3), k1, 31), k2, 32)");

  v = mkTerm<expr::mpz_class>(33, efac);
  map = finite_map::set(map, key3, v);
  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "set(set(set(defk(k1, k2, k3), k1, 31), k2, 32), k3, 33)");
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

  keys.push_back(bind::intConst(mkTerm<std::string>("k2", efac)));
  lambda_keys = finite_map::make_lambda_map_keys(keys, efac);

  CHECK(boost::lexical_cast<std::string>(lambda_keys) ==
        "(lambda (INT) ite(k2=(B0:INT), 2, ite(k1=(B0:INT), 1, 0)))");

  keys.push_back(bind::intConst(mkTerm<std::string>("k3", efac)));
  lambda_keys = finite_map::make_lambda_map_keys(keys, efac);

  CHECK(boost::lexical_cast<std::string>(lambda_keys) ==
        "(lambda (INT) ite(k3=(B0:INT), 3, ite(k2=(B0:INT), 2, "
        "ite(k1=(B0:INT), 1, 0))))");
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
}
