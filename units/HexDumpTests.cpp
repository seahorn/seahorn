#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#include "doctest.h"

#include "boost/lexical_cast.hpp"

#include "llvm/ADT/APInt.h"
#include "llvm/Support/raw_ostream.h"

#include <regex>
#include <string>

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprGmp.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"
#include "seahorn/Expr/HexDump.hh"

#include "seahorn/Support/SeaDebug.h"

using namespace expr;
using namespace llvm;
using namespace hexDump;

template <class ExpectedIt, class ActualIt>
void checkPairs(ExpectedIt expectedBegin, ExpectedIt expectedEnd,
                ActualIt actualBegin, ActualIt actualEnd) {
  CHECK(std::distance(expectedBegin, expectedEnd) ==
        std::distance(actualBegin, actualEnd));

  for (; expectedBegin != expectedEnd && actualBegin != actualEnd;
       expectedBegin++, actualBegin++) {

    CHECK((*expectedBegin) == (*actualBegin));
  }
}

void populateBvNumArr(Expr &e, ExprFactory &efac, std::vector<KeyValue> &kvList,
                      mpz_class idxNum, mpz_class valueNum,
                      unsigned width = 16) {
  kvList.push_back(KeyValue(mkTerm<mpz_class>(idxNum, efac),
                            mkTerm<mpz_class>(valueNum, efac)));
  e = array::store(e, bv::bvnum(idxNum, width, efac),
                   bv::bvnum(valueNum, width, efac));
}

TEST_CASE("hexDumpBvNum.test") {
  ExprFactory efac;

  Expr intSort = sort::intTy(efac);
  Expr bvSort = bv::bvsort(16, efac);

  std::vector<KeyValue> kvList;
  Expr defaultValue = bv::bvnum(0x1417, 16, efac);
  Expr e = array::constArray(bvSort, defaultValue);
  defaultValue = defaultValue->first(); // MPZ term

  populateBvNumArr(e, efac, kvList, 2, 84);
  kvList.push_back(KeyValue(mkTerm<mpz_class>(4, efac), defaultValue,
                            true)); // filler KeyValue
  populateBvNumArr(e, efac, kvList, 8, 101);
  kvList.push_back(KeyValue(mkTerm<mpz_class>(10, efac), defaultValue,
                            true)); // filler KeyValue
  populateBvNumArr(e, efac, kvList, 24, 115);
  kvList.push_back(KeyValue(mkTerm<mpz_class>(26, efac), defaultValue,
                            true)); // filler KeyValue
  populateBvNumArr(e, efac, kvList, 30, 116);

  HexDump hd(e, 2);
  llvm::errs() << hd;
  // // std::cout<<hd;
  // hd.dump(std::cout, false);
  std::string outcome = boost::lexical_cast<std::string>(hd);
  outcome = std::regex_replace(outcome, std::regex(" *\n *"), "");

  std::string expected = "0002: 00 54  |.T|\
0004: 14 17  |..|\
*\
0008: 00 65  |.e|\
000a: 14 17  |..|\
*\
0018: 00 73  |.s|\
001a: 14 17  |..|\
*\
001e: 00 74  |.t|";

  CHECK(outcome == expected);
  checkPairs(kvList.cbegin(), kvList.cend(), hd.cbegin(), hd.cend());
}

TEST_CASE("num.test") {
  ExprFactory efac;

  Expr intSort = sort::intTy(efac);

  Expr e = array::constArray(intSort, mkTerm<unsigned>(5, efac));
  e = array::store(e, mkTerm<unsigned>(0, efac), mkTerm<unsigned>(16, efac));
  e = array::store(e, mkTerm<unsigned>(4, efac), mkTerm<unsigned>(1, efac));
  e = array::store(e, mkTerm<unsigned>(12, efac), mkTerm<unsigned>(2, efac));

  llvm::errs() << "Expression: " << *e;

  HexDump hd(e, 4);
  // // std::cout<<hd;
  llvm::errs() << hd << "\n";

  std::string outcome = boost::lexical_cast<std::string>(hd);
  outcome = std::regex_replace(outcome, std::regex(" *\n *"), "");

  std::string expected = "0: 10  |.|\
4: 01  |.|\
8: 05  |.|\
c: 02  |.|";

  CHECK(outcome == expected);

  //-----------

  e = array::constArray(intSort, mkTerm<mpz_class>(0x12345678, efac));
  e = array::store(e, mkTerm<mpz_class>(0x100000, efac),
                   mkTerm<mpz_class>(0x111111, efac));
  e = array::store(e, mkTerm<mpz_class>(0x10000c, efac),
                   mkTerm<mpz_class>(0, efac));
  e = array::store(e, mkTerm<mpz_class>(0x100010, efac),
                   mkTerm<mpz_class>(0x334455, efac));

  llvm::errs() << "Expression: " << *e;

  HexDump hd2(e, 2);
  llvm::errs() << hd2 << "\n";

  outcome = boost::lexical_cast<std::string>(hd2);
  outcome = std::regex_replace(outcome, std::regex(" *\n *"), "");

  expected = "100000: 00 11 11 11  |....|\
100002: 12 34 56 78  |.4Vx|\
*\
10000c: 00 00 00 00  |....|\
10000e: 12 34 56 78  |.4Vx|\
100010: 00 33 44 55  |.3DU|";

  CHECK(outcome == expected);
}

TEST_CASE("finiteMap.test") {
  ExprFactory efac;
  ExprVector keys;
  keys.push_back(mkTerm<mpz_class>(0x50000a, efac));
  keys.push_back(mkTerm<mpz_class>(0x500000, efac));
  keys.push_back(mkTerm<mpz_class>(0x500002, efac));

  ExprVector values;
  values.push_back(mkTerm<mpz_class>(0xffffaa, efac));
  values.push_back(mkTerm<mpz_class>(0x12345, efac));
  values.push_back(mkTerm<mpz_class>(0xaaaa1, efac));

  Expr e = finite_map::constFiniteMap(keys, values);
  e = finite_map::set(e, mkTerm<mpz_class>(0x500010, efac),
                      mkTerm<mpz_class>(4, efac));
  e = finite_map::set(e, mkTerm<mpz_class>(0x500010, efac),
                      mkTerm<mpz_class>(10, efac));
  // note: e does not have a default value so the hex dumper will not fill in
  // any gaps

  llvm::errs() << "Expression: " << *e;

  HexDump hd(e, 2);
  llvm::errs() << hd;

  std::string outcome = boost::lexical_cast<std::string>(hd);
  outcome = std::regex_replace(outcome, std::regex(" *\n *"), "");

  std::string expected = "500000: 01 23 45  |.#E|\
500002: 0a aa a1  |...|\
50000a: ff ff aa  |...|\
500010: 00 00 0a  |...|";

  CHECK(outcome == expected);
}

TEST_CASE("ite.test") {
  ExprFactory efac;
  Expr a = bind::intConst(mkTerm<std::string>("a", efac));

  Expr eq1 = mk<EQ>(mkTerm<mpz_class>(10, efac), a);
  Expr eq2 = mk<EQ>(mkTerm<mpz_class>(2, efac), a);

  Expr ite =
      mk<ITE>(eq1, mkTerm<mpz_class>(0x3, efac), mkTerm<mpz_class>(1, efac));
  ite = mk<ITE>(eq2, mkTerm<mpz_class>(0x5a, efac), ite);

  llvm::errs() << "Expression: " << *ite;
  printIteTree(ite);

  HexDump hd(ite);
  llvm::errs() << hd;

  std::vector<KeyValue> kvList;
  kvList.push_back(
      KeyValue(mkTerm<mpz_class>(2, efac), mkTerm<mpz_class>(90, efac)));
  kvList.push_back(
      KeyValue(mkTerm<mpz_class>(10, efac), mkTerm<mpz_class>(3, efac)));

  checkPairs(kvList.begin(), kvList.end(), hd.cbegin(), hd.cend());

  std::string outcome = boost::lexical_cast<std::string>(hd);
  outcome = std::regex_replace(outcome, std::regex(" *\n *"), "");

  std::string expected = "2: 5a  |Z|\
a: 03  |.|";

  CHECK(outcome == expected);

  //----------

  eq1 = mk<NEQ>(mkTerm<unsigned>(20, efac), a);
  eq2 = mk<NEQ>(mkTerm<unsigned>(5, efac), a);
  Expr eq3 = mk<NEQ>(mkTerm<unsigned>(40, efac), a);

  ite = mk<ITE>(eq1, a, mkTerm<mpz_class>(0x12345, efac));
  ite = mk<ITE>(eq2, ite, mkTerm<mpz_class>(0x114232, efac));
  ite = mk<ITE>(eq3, ite, mkTerm<mpz_class>(0xaa3fde, efac));

  llvm::errs() << "Expression: " << *ite;
  printIteTree(ite);

  HexDump hd2(ite);
  llvm::errs() << hd2;

  kvList.clear();
  kvList.push_back(
      KeyValue(mkTerm<unsigned>(5, efac), mkTerm<mpz_class>(0x114232, efac)));
  kvList.push_back(
      KeyValue(mkTerm<unsigned>(20, efac), mkTerm<mpz_class>(0x12345, efac)));
  kvList.push_back(
      KeyValue(mkTerm<unsigned>(40, efac), mkTerm<mpz_class>(0xaa3fde, efac)));

  checkPairs(kvList.begin(), kvList.end(), hd2.cbegin(), hd2.cend());

  // -------------------

  eq1 = mk<NEQ>(mkTerm<mpz_class>(0x200000, efac), a);
  eq2 = mk<EQ>(mkTerm<mpz_class>(0x200004, efac), a);

  ite = mk<ITE>(eq1, a, mkTerm<mpz_class>(0xaaaa1234, efac));
  ite = mk<ITE>(eq2, mkTerm<mpz_class>(0xbbbb1111, efac), ite);

  llvm::errs() << "Expression: " << *ite;
  printIteTree(ite);

  HexDump hd3(ite);
  llvm::errs() << hd3;

  kvList.clear();
  kvList.push_back(KeyValue(mkTerm<mpz_class>(0x200000, efac),
                            mkTerm<mpz_class>(0xaaaa1234, efac)));
  kvList.push_back(KeyValue(mkTerm<mpz_class>(0x200004, efac),
                            mkTerm<mpz_class>(0xbbbb1111, efac)));

  checkPairs(kvList.begin(), kvList.end(), hd3.cbegin(), hd3.cend());
}

TEST_CASE("lambda.test") {

  ExprFactory efac;

  Expr intSort = sort::intTy(efac);

  Expr intConst = bind::intConst(mkTerm<std::string>("intConst", efac));

  Expr intBound0 = bind::bvar(0, intSort);
  Expr intBound1 = bind::bvar(1, intSort);

  Expr eq1 = mk<EQ>(intBound0, mkTerm<mpz_class>(0, efac));
  Expr eq2 = mk<EQ>(mkTerm<mpz_class>(2, efac), intBound1);

  Expr ite = mk<ITE>(eq1, bv::bvnum(0x345672, 32, efac), intBound1);
  ite = mk<ITE>(eq2, bv::bvnum(0x4, 32, efac),
                ite); // only b and d are actually reachable

  Expr lambda = mk<LAMBDA>(intConst, intConst, ite);

  llvm::errs() << "Expression: " << *lambda << "\n";
  printIteTree(ite);

  HexDump hd(ite);
  llvm::errs() << hd;

  std::vector<KeyValue> kvList;
  kvList.push_back(
      KeyValue(mkTerm<mpz_class>(0, efac), mkTerm<mpz_class>(0x345672, efac)));
  kvList.push_back(
      KeyValue(mkTerm<mpz_class>(2, efac), mkTerm<mpz_class>(4, efac)));

  checkPairs(kvList.begin(), kvList.end(), hd.cbegin(), hd.cend());
}

TEST_CASE("struct.test") {

  ExprFactory efac;

  Expr intSort = sort::intTy(efac);
  Expr bvSort = bv::bvsort(16, efac);

  std::vector<KeyValue> kvList;
  Expr defaultValue = bv::bvnum(0x61626364, 32, efac);
  Expr e1 = array::constArray(bvSort, defaultValue);
  defaultValue = defaultValue->first(); // MPZ term

  populateBvNumArr(e1, efac, kvList, 0xa00000, 0x99999, 32);
  populateBvNumArr(e1, efac, kvList, 0xa00001, 116, 32);
  kvList.push_back(KeyValue(mkTerm<mpz_class>(0xa00002, efac), defaultValue,
                            false)); // filler KeyValue
  populateBvNumArr(e1, efac, kvList, 0xa00003, 0x30313233, 32);

  //-----------------

  std::vector<KeyValue> pairList2;

  Expr intConst = bind::intConst(mkTerm<std::string>("intConst", efac));

  Expr intBound0 = bind::bvar(0, intSort);
  Expr intBound1 = bind::bvar(1, intSort);

  Expr eq1 = mk<EQ>(mkTerm<mpz_class>(0, efac), intBound0);
  Expr eq2 = mk<EQ>(mkTerm<mpz_class>(2, efac), intBound0);
  Expr eq3 = mk<EQ>(intBound1, mkTerm<mpz_class>(1, efac));

  Expr ite = mk<ITE>(eq1, mkTerm<mpz_class>(0x4365ffab, efac),
                     mkTerm<mpz_class>(4, efac));
  ite = mk<ITE>(eq2, mkTerm<mpz_class>(0x67a56b, efac), ite);
  ite = mk<ITE>(eq3, mkTerm<mpz_class>(0x9088dd, efac), ite);

  pairList2.push_back(KeyValue(mkTerm<mpz_class>(0, efac),
                               mkTerm<mpz_class>(0x4365ffab, efac)));
  pairList2.push_back(
      KeyValue(mkTerm<mpz_class>(1, efac), mkTerm<mpz_class>(0x9088dd, efac)));
  pairList2.push_back(
      KeyValue(mkTerm<mpz_class>(2, efac), mkTerm<mpz_class>(0x67a56b, efac)));

  Expr e2 = mk<LAMBDA>(intConst, intConst, ite);

  //--------------

  llvm::errs() << "Child 1: " << *e1 << "\n";
  llvm::errs() << "Child 2: " << *e2 << "\n";
  printIteTree(ite);

  Expr strct = mk<MK_STRUCT>(e1, e2);
  llvm::errs() << "Struct: " << *strct << "\n";

  StructHexDump hd(strct);
  llvm::errs() << hd;

  std::vector<const_hd_range> ranges = hd.getRanges();

  CHECK(ranges.size() == 2);

  checkPairs(kvList.begin(), kvList.end(), ranges.at(0).begin(),
             ranges.at(0).end()); // child 1 : bv checkPairs

  checkPairs(pairList2.begin(), pairList2.end(), ranges.at(1).begin(),
             ranges.at(1).end()); // child 2 : ite
}