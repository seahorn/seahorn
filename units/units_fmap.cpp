/**==-- Finite Maps Expr Tests --==*/
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#include "doctest.h"

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/ExprOpBv.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"
#include "seahorn/Expr/Smt/EZ3.hh"

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

TEST_CASE("expr.finite_map.create_map") {

  ExprFactory efac;
  Expr map =
      mkConstFiniteMap({mkIntKey(1, efac)}, mkInt(0, efac), {mkInt(1, efac)});

  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "defmap(defk(k1), fmap-default(0), defv(1))");

  map = mkConstFiniteMap({mkBvKey(1, 32, efac)}, mkBvNum(0, 64, efac));

  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "defmap(defk(j1), fmap-default(0:bv(64)), defv(0:bv(64)))");
}

TEST_CASE("expr.finite_map.create_init_map") {

  ExprFactory efac;

  ExprVector ks = {mkIntKey(1, efac), mkIntKey(2, efac), mkIntKey(3, efac)};
  ExprVector values = {mkInt(41, efac), mkInt(42, efac), mkInt(43, efac)};

  Expr map = fmap::constFiniteMap(ks, mkInt(0, efac), values);

  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "defmap(defk(k1, k2, k3), fmap-default(0), defv(41, 42, 43))");
}

TEST_CASE("expr.finite_map.set") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);

  Expr map =
      fmap::set(mkConstFiniteMap({k1}, mkInt(0, efac), {mkInt(20, efac)}), k1,
                mkInt(30, efac));

  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "defmap(defk(k1), fmap-default(0), defv(30))");
}

TEST_CASE("expr.finite_map.get") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);
  Expr eget = fmap::get(mkConstFiniteMap({k1}, mkInt(0, efac)), k1);

  CHECK(eget);
  CHECK(boost::lexical_cast<std::string>(*eget) == "0");
}

TEST_CASE("expr.finite_map.create_set_3") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);
  Expr k2 = mkIntKey(2, efac);
  Expr k3 = mkIntKey(3, efac);

  Expr map =
      mkConstFiniteMap({k1, k2, k3}, mkInt(0, efac),
                       {mkInt(41, efac), mkInt(42, efac), mkInt(43, efac)});
  map = fmap::set(map, k1, mkInt(31, efac));

  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "defmap(defk(k1, k2, k3), fmap-default(0), defv(31, 42, 43))");

  map = fmap::set(map, k2, mkInt(32, efac));
  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "defmap(defk(k1, k2, k3), fmap-default(0), defv(ite(k1=k2, 32, 31), "
        "32, 43))");

  map = fmap::set(map, k3, mkInt(33, efac));
  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "defmap(defk(k1, k2, k3), fmap-default(0), defv(ite(k1=k3, 33, "
        "ite(k1=k2, 32, 31)), ite(k2=k3, 33, 32), 33))");
}

TEST_CASE("expr.finite_map.set_num_ks") {

  ExprFactory efac;

  Expr k1 = mkInt(1, efac);
  Expr k2 = mkInt(2, efac);
  Expr k3 = mkInt(3, efac);

  ExprVector ks = {k1, k2, k3};
  ExprVector values = {mkInt(41, efac), mkInt(42, efac), mkInt(43, efac)};

  Expr map = fmap::constFiniteMap(ks, mkInt(0, efac), values);
  map = fmap::set(map, k1, mkInt(31, efac));

  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "defmap(defk(1, 2, 3), fmap-default(0), defv(31, 42, 43))");

  map = fmap::set(map, k2, mkInt(32, efac));
  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "defmap(defk(1, 2, 3), fmap-default(0), defv(31, 32, 43))");

  map = fmap::set(map, k3, mkInt(33, efac));
  CHECK(map);
  CHECK(boost::lexical_cast<std::string>(*map) ==
        "defmap(defk(1, 2, 3), fmap-default(0), defv(31, 32, 33))");
}

TEST_CASE("expr.finite_map.set") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);

  ExprVector ks = {k1, mkIntKey(2, efac), mkIntKey(3, efac)};
  ExprVector values = {mkInt(1, efac), mkInt(2, efac), mkInt(3, efac)};

  Expr map = mkConstFiniteMap(ks, mkInt(0, efac), values);
  // set the value of k1
  map = fmap::set(map, k1, mkInt(42, efac));

  CHECK(boost::lexical_cast<std::string>(map) ==
        "defmap(defk(k1, k2, k3), fmap-default(0), defv(42, 2, 3))");

  errs() << "map: " << *map << "\n";
  Expr v = fmap::get(map, k1);

  EZ3 z3(efac);
  errs() << "Simplified: " << *z3_simplify(z3, v) << "\n";
}

TEST_CASE("expr.finite_map.get_after_set") {

  ExprFactory efac;

  Expr k1 = mkIntKey(1, efac);
  ExprVector ks = {k1, mkIntKey(2, efac), mkIntKey(3, efac)};
  ExprVector vs = {mkInt(1, efac), mkInt(2, efac), mkInt(3, efac)};

  Expr map = mkConstFiniteMap(ks, mkInt(0, efac), vs);
  map = fmap::set(map, k1, mkInt(42, efac));

  CHECK(boost::lexical_cast<std::string>(map) ==
        "defmap(defk(k1, k2, k3), fmap-default(0), defv(42, 2, 3))");

  Expr get_value = fmap::get(map, k1);

  CHECK(boost::lexical_cast<std::string>(get_value) == "42");
}

TEST_CASE("expr.finite_map.fm_type_declaration") {

  ExprFactory efac;
  ExprVector ks = {mkIntKey(1, efac)};
  Expr fmTy = sort::finiteMapTy(sort::intTy(efac), ks);
  CHECK(isOpX<FINITE_MAP_TY>(fmTy));
  CHECK(isOpX<FINITE_MAP_KEYS_TY>(sort::finiteMapKeyTy(fmTy)));

  ks.push_back(mkIntKey(5, efac));
  fmTy = sort::finiteMapTy(bv::bvsort(64, efac), ks);

  CHECK(isOpX<FINITE_MAP_TY>(fmTy));
  CHECK(isOpX<FINITE_MAP_KEYS_TY>(sort::finiteMapKeyTy(fmTy)));
}
