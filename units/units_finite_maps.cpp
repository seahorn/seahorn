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
  Expr map1 = finite_map::set(map, key1, v);

  CHECK(map1);
  CHECK(boost::lexical_cast<std::string>(*map1) == "set(defk(k1), k1, 30)");

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

  Expr eget = finite_map::get(map, key1);

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

  Expr map = finite_map::constFiniteMap(keys);

  Expr v = mkTerm<expr::mpz_class>(31, efac);
  map = finite_map::set(map, key1, v);

  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "set(defk(k1, k2, k3), k1, 31)");

  errs() << *map << "\n";

  v = mkTerm<expr::mpz_class>(32, efac);
  map = finite_map::set(map, key2, v);
  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "set(set(defk(k1, k2, k3), k1, 31), k2, 32)");

  errs() << *map << "\n";

  v = mkTerm<expr::mpz_class>(33, efac);
  map = finite_map::set(map, key3, v);
  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "set(set(set(defk(k1, k2, k3), k1, 31), k2, 32), k3, 33)");

  errs() << *map << "\n";
}
