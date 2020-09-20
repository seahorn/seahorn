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
                      mpz_class idxNum, mpz_class valueNum, unsigned keyWidth,
                      unsigned valueWidth) {
  kvList.push_back(KeyValue(mkTerm<mpz_class>(idxNum, efac),
                            mkTerm<mpz_class>(valueNum, efac)));
  e = array::store(e, bv::bvnum(idxNum, keyWidth, efac),
                   bv::bvnum(valueNum, valueWidth, efac));
}

TEST_CASE("hexDumpBvNum.test") {
  ExprFactory efac;

  Expr intSort = sort::intTy(efac);
  Expr bvSort = bv::bvsort(16, efac);

  std::vector<KeyValue> kvList;
  Expr defaultValue = bv::bvnum(0x1417, 16, efac);

  Expr e = array::constArray(bvSort, defaultValue);
  Expr defaultValueNum = defaultValue->first(); // MPZ term

  populateBvNumArr(e, efac, kvList, 2, 84, 16, 16);
  kvList.push_back(KeyValue(mkTerm<mpz_class>(4, efac), defaultValueNum,
                            true)); // filler KeyValue
  populateBvNumArr(e, efac, kvList, 8, 101, 16, 16);
  kvList.push_back(KeyValue(mkTerm<mpz_class>(10, efac), defaultValueNum,
                            true)); // filler KeyValue
  populateBvNumArr(e, efac, kvList, 24, 115, 16, 16);
  kvList.push_back(KeyValue(mkTerm<mpz_class>(26, efac), defaultValueNum,
                            true)); // filler KeyValue
  populateBvNumArr(e, efac, kvList, 30, 116, 16, 16);

  HexDump hd(e);
  llvm::errs() << hd << "\n";
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

  //------
  defaultValue = bv::bvnum(0x14, 16, efac);

  e = array::constArray(bvSort, defaultValue);

  kvList.clear();
  populateBvNumArr(e, efac, kvList, 4, 12, 32, 32);
  kvList.push_back(KeyValue(mkTerm<mpz_class>(8, efac), defaultValue,
                            false)); // filler KeyValue
  populateBvNumArr(e, efac, kvList, 12, 84, 32, 32);

  HexDump hd2(e);
  llvm::errs() << hd2 << "\n";
  outcome = boost::lexical_cast<std::string>(hd2);
  outcome = std::regex_replace(outcome, std::regex(" *\n *"), "");

  expected = "00000004: 00 00 00 0c  |....|\
00000008: 00 00 00 14  |....|\
0000000c: 00 00 00 54  |...T|";

  CHECK(outcome == expected);
  checkPairs(kvList.cbegin(), kvList.cend(), hd2.cbegin(), hd2.cend());
}

TEST_CASE("bvNumNotAligned.test") {
  ExprFactory efac;

  Expr intSort = sort::intTy(efac);
  Expr bvSort = bv::bvsort(16, efac);

  std::vector<KeyValue> kvList;
  Expr defaultValue = bv::bvnum(0xffff1234, 64, efac);

  Expr e = array::constArray(bvSort, defaultValue);
  Expr defaultValueNum = defaultValue->first(); // MPZ term

  populateBvNumArr(e, efac, kvList, 3, 0x4567aabb, 32, 64);
  kvList.push_back(KeyValue(mkTerm<mpz_class>(4, efac), defaultValueNum,
                            true)); // filler KeyValue
  populateBvNumArr(e, efac, kvList, 7, 0x656f, 32, 64);
  kvList.push_back(KeyValue(mkTerm<mpz_class>(8, efac), defaultValueNum,
                            true)); // filler KeyValue
  populateBvNumArr(e, efac, kvList, 11, 115, 32, 64);

  HexDump hd(e);
  llvm::errs() << hd << "\n";
  std::string outcome = boost::lexical_cast<std::string>(hd);
  outcome = std::regex_replace(outcome, std::regex(" *\n *"), "");

  std::string expected = "00000003: 00 00 00 00 45 67 aa bb  |....Eg..|\
00000004: 00 00 00 00 ff ff 12 34  |.......4|\
*\
00000007: 00 00 00 00 00 00 65 6f  |......eo|\
00000008: 00 00 00 00 ff ff 12 34  |.......4|\
*\
0000000b: 00 00 00 00 00 00 00 73  |.......s|";

  CHECK(outcome == expected);
  checkPairs(kvList.cbegin(), kvList.cend(), hd.cbegin(), hd.cend());
}
TEST_CASE("num.test") {
  ExprFactory efac;

  Expr intSort = sort::intTy(efac);

  Expr e = array::constArray(intSort, mkTerm<unsigned>(5, efac));
  e = array::store(e, mkTerm<unsigned>(0, efac),
                   mkTerm<unsigned>(0xabcd1212, efac));
  e = array::store(e, mkTerm<unsigned>(2, efac), mkTerm<unsigned>(1, efac));
  e = array::store(e, mkTerm<unsigned>(3, efac), mkTerm<unsigned>(2, efac));

  llvm::errs() << "Expression: " << *e;

  HexDump hd(e);
  // std::cout<<hd;
  llvm::errs() << hd << "\n";

  std::string outcome = boost::lexical_cast<std::string>(hd);
  outcome = std::regex_replace(outcome, std::regex(" *\n *"), "");

  std::string expected = "00: ab cd 12 12  |....|\
01: 00 00 00 05  |....|\
02: 00 00 00 01  |....|\
03: 00 00 00 02  |....|";

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

  HexDump hd2(e);
  llvm::errs() << hd2 << "\n";

  outcome = boost::lexical_cast<std::string>(hd2);
  outcome = std::regex_replace(outcome, std::regex(" *\n *"), "");

  expected = "100000: 00 11 11 11  |....|\
100001: 12 34 56 78  |.4Vx|\
*\
10000c: 00 00 00 00  |....|\
10000d: 12 34 56 78  |.4Vx|\
*\
100010: 00 33 44 55  |.3DU|";

  CHECK(outcome == expected);
}

TEST_CASE("finiteMap.test") {
  ExprFactory efac;
  ExprVector keys;
  std::vector<KeyValue> kvList;

  keys.push_back(mkTerm<mpz_class>(0x50000a, efac));
  keys.push_back(mkTerm<mpz_class>(0x500000, efac));
  keys.push_back(mkTerm<mpz_class>(0x500002, efac));

  ExprVector values;
  values.push_back(mkTerm<mpz_class>(0xffaa, efac));
  values.push_back(mkTerm<mpz_class>(0x2345, efac));
  values.push_back(mkTerm<mpz_class>(0xaaa1, efac));

  Expr e = finite_map::constFiniteMap(keys, values);
  e = finite_map::set(e, mkTerm<mpz_class>(0x500010, efac),
                      mkTerm<mpz_class>(4, efac));
  e = finite_map::set(e, mkTerm<mpz_class>(0x500010, efac),
                      mkTerm<mpz_class>(10, efac));
  // note: e does not have a default value so the hex dumper will not fill in
  // any gaps

  llvm::errs() << "Expression: " << *e;

  HexDump hd(e);
  llvm::errs() << hd;

  std::string outcome = boost::lexical_cast<std::string>(hd);
  outcome = std::regex_replace(outcome, std::regex(" *\n *"), "");

  std::string expected = "500000: 23 45  |#E|\
500002: aa a1  |..|\
50000a: ff aa  |..|\
500010: 00 0a  |..|";

  CHECK(outcome == expected);

  kvList.push_back(KeyValue(mkTerm<mpz_class>(0x500000, efac),
                            mkTerm<mpz_class>(0x2345, efac)));
  kvList.push_back(KeyValue(mkTerm<mpz_class>(0x500002, efac),
                            mkTerm<mpz_class>(0xaaa1, efac)));
  kvList.push_back(KeyValue(mkTerm<mpz_class>(0x50000a, efac),
                            mkTerm<mpz_class>(0xffaa, efac)));
  kvList.push_back(KeyValue(mkTerm<mpz_class>(0x500010, efac),
                            mkTerm<mpz_class>(0xa, efac)));

  checkPairs(kvList.cbegin(), kvList.cend(), hd.cbegin(), hd.cend());
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
      KeyValue(mkTerm<mpz_class>(2, efac), mkTerm<mpz_class>(0x5a, efac)));
  kvList.push_back(KeyValue(mkTerm<mpz_class>(3, efac),
                            mkTerm<mpz_class>(0x01, efac), true));
  kvList.push_back(
      KeyValue(mkTerm<mpz_class>(0xa, efac), mkTerm<mpz_class>(3, efac)));

  checkPairs(kvList.begin(), kvList.end(), hd.cbegin(), hd.cend());

  std::string outcome = boost::lexical_cast<std::string>(hd);
  outcome = std::regex_replace(outcome, std::regex(" *\n *"), "");

  std::string expected = "02: 5a  |Z|\
03: 01  |.|\
*\
0a: 03  |.|";

  CHECK(outcome == expected);

  //----------

  eq1 = mk<NEQ>(mkTerm<unsigned>(20, efac), a);
  eq2 = mk<NEQ>(mkTerm<unsigned>(4, efac), a);
  Expr eq3 = mk<NEQ>(mkTerm<unsigned>(40, efac), a);

  ite = mk<ITE>(eq1, mkTerm<mpz_class>(0x0, efac),
                mkTerm<mpz_class>(0x12345, efac));
  ite = mk<ITE>(eq2, ite, mkTerm<mpz_class>(0x114232, efac));
  ite = mk<ITE>(eq3, ite, mkTerm<mpz_class>(0xaa3fde00, efac));

  llvm::errs() << "Expression: " << *ite;
  printIteTree(ite);

  HexDump hd2(ite);
  llvm::errs() << hd2;

  kvList.clear();
  kvList.push_back(
      KeyValue(mkTerm<unsigned>(4, efac), mkTerm<mpz_class>(0x114232, efac)));
  kvList.push_back(
      KeyValue(mkTerm<unsigned>(5, efac), mkTerm<mpz_class>(0x0, efac), true));
  kvList.push_back(
      KeyValue(mkTerm<unsigned>(20, efac), mkTerm<mpz_class>(0x12345, efac)));
  kvList.push_back(
      KeyValue(mkTerm<unsigned>(21, efac), mkTerm<mpz_class>(0x0, efac), true));
  kvList.push_back(KeyValue(mkTerm<unsigned>(40, efac),
                            mkTerm<mpz_class>(0xaa3fde00, efac)));

  checkPairs(kvList.begin(), kvList.end(), hd2.cbegin(), hd2.cend());

  // // -------------------

  eq1 = mk<NEQ>(mkTerm<mpz_class>(0x200000, efac), a);
  eq2 = mk<EQ>(mkTerm<mpz_class>(0x200001, efac), a);

  ite = mk<ITE>(eq1, mkTerm<mpz_class>(0x9, efac),
                mkTerm<mpz_class>(0xaaaa1234, efac));
  ite = mk<ITE>(eq2, mkTerm<mpz_class>(0xbbbb1111, efac), ite);

  llvm::errs() << "Expression: " << *ite;
  printIteTree(ite);

  HexDump hd3(ite);
  llvm::errs() << hd3;

  kvList.clear();
  kvList.push_back(KeyValue(mkTerm<mpz_class>(0x200000, efac),
                            mkTerm<mpz_class>(0xaaaa1234, efac)));
  kvList.push_back(KeyValue(mkTerm<mpz_class>(0x200001, efac),
                            mkTerm<mpz_class>(0xbbbb1111, efac)));

  checkPairs(kvList.begin(), kvList.end(), hd3.cbegin(), hd3.cend());

  //---------------

  eq1 = mk<EQ>(bv::bvnum(0x44, 32, efac), a);
  eq2 = mk<EQ>(mkTerm<mpz_class>(0x78, efac), a);

  ite = mk<ITE>(eq1, bv::bvnum(0x6672, 32, efac), bv::bvnum(0x4444, 32, efac));
  ite = mk<ITE>(eq2, mkTerm<mpz_class>(0xbbbb, efac), ite);

  llvm::errs() << "Expression: " << *ite;
  printIteTree(ite);

  HexDump hd4(ite);
  llvm::errs() << hd4;

  kvList.clear();
  kvList.push_back(
      KeyValue(mkTerm<mpz_class>(0x44, efac), mkTerm<mpz_class>(0x6672, efac)));
  kvList.push_back(KeyValue(mkTerm<mpz_class>(0x45, efac),
                            mkTerm<mpz_class>(0x4444, efac), true));
  kvList.push_back(
      KeyValue(mkTerm<mpz_class>(0x78, efac), mkTerm<mpz_class>(0xbbbb, efac)));

  checkPairs(kvList.begin(), kvList.end(), hd4.cbegin(), hd4.cend());
}

TEST_CASE("lambda.test") {

  ExprFactory efac;

  Expr intSort = sort::intTy(efac);

  Expr intConst = bind::intConst(mkTerm<std::string>("intConst", efac));

  Expr intBound0 = bind::bvar(0, intSort);
  Expr intBound1 = bind::bvar(1, intSort);

  Expr eq1 = mk<EQ>(intBound0, mkTerm<mpz_class>(0, efac));
  Expr eq2 = mk<EQ>(mkTerm<mpz_class>(2, efac), intBound1);

  Expr ite = mk<ITE>(eq1, bv::bvnum(0x2, 8, efac), bv::bvnum(0xff, 8, efac));
  ite = mk<ITE>(eq2, bv::bvnum(0x4, 8, efac),
                ite); // only b and d are actually reachable

  Expr lambda = mk<LAMBDA>(intConst, intConst, ite);

  llvm::errs() << "Expression: " << *lambda << "\n";
  printIteTree(ite);

  HexDump hd(ite);
  llvm::errs() << hd;

  std::vector<KeyValue> kvList;
  kvList.push_back(
      KeyValue(mkTerm<mpz_class>(0, efac), mkTerm<mpz_class>(0x2, efac)));
  kvList.push_back(
      KeyValue(mkTerm<mpz_class>(1, efac), mkTerm<mpz_class>(0xff, efac)));
  kvList.push_back(
      KeyValue(mkTerm<mpz_class>(2, efac), mkTerm<mpz_class>(4, efac)));

  checkPairs(kvList.begin(), kvList.end(), hd.cbegin(), hd.cend());
}

TEST_CASE("struct.test") {

  ExprFactory efac;

  Expr intSort = sort::intTy(efac);
  Expr bvSort = bv::bvsort(16, efac);

  std::vector<KeyValue> kvList;
  Expr defaultValue = bv::bvnum(0x61, 32, efac);
  Expr e1 = array::constArray(bvSort, defaultValue);
  defaultValue = defaultValue->first(); // MPZ term

  populateBvNumArr(e1, efac, kvList, 0xa00000, 0x99, 32, 32);
  populateBvNumArr(e1, efac, kvList, 0xa00001, 116, 32, 32);
  kvList.push_back(KeyValue(mkTerm<mpz_class>(0xa00002, efac), defaultValue,
                            false)); // filler KeyValue
  populateBvNumArr(e1, efac, kvList, 0xa00003, 0x30, 32, 32);

  //-----------------

  std::vector<KeyValue> pairList2;

  Expr intConst = bind::intConst(mkTerm<std::string>("intConst", efac));

  Expr intBound0 = bind::bvar(0, intSort);
  Expr intBound1 = bind::bvar(1, intSort);

  Expr eq1 = mk<EQ>(mkTerm<mpz_class>(0, efac), intBound0);
  Expr eq2 = mk<EQ>(mkTerm<mpz_class>(2, efac), intBound0);
  Expr eq3 = mk<EQ>(intBound1, mkTerm<mpz_class>(1, efac));

  Expr ite =
      mk<ITE>(eq1, mkTerm<mpz_class>(0x43, efac), mkTerm<mpz_class>(4, efac));
  ite = mk<ITE>(eq2, mkTerm<mpz_class>(0x67, efac), ite);
  ite = mk<ITE>(eq3, mkTerm<mpz_class>(0x90, efac), ite);

  pairList2.push_back(
      KeyValue(mkTerm<mpz_class>(0, efac), mkTerm<mpz_class>(0x43, efac)));
  pairList2.push_back(
      KeyValue(mkTerm<mpz_class>(1, efac), mkTerm<mpz_class>(0x90, efac)));
  pairList2.push_back(
      KeyValue(mkTerm<mpz_class>(2, efac), mkTerm<mpz_class>(0x67, efac)));

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
TEST_CASE("specialCases.test") {
  ExprFactory efac;
  Expr intConst = bind::intConst(mkTerm<std::string>("intConst", efac));
  Expr intConst2 = bind::intConst(mkTerm<std::string>("intConst2", efac));
  Expr intConst3 = bind::intConst(mkTerm<std::string>("intConst3", efac));
  Expr intSort = sort::intTy(efac);

  // doesn't have anything that is supported by the
  // hex dump so the result should be same as input
  Expr e = mk<AND>(intConst, intConst);

  llvm::errs() << "Expression: " << *e << "\n";

  HexDump hd(e);
  llvm::errs() << hd;

  std::string outcome = boost::lexical_cast<std::string>(hd);
  std::string expected = boost::lexical_cast<std::string>(*e);

  CHECK(outcome == expected);

  CHECK(hd.cbegin() == hd.cend());

  //-------------

  std::vector<KeyValue> kvList;
  Expr bvSort32 = bv::bvsort(32, efac);
  e = array::constArray(
      bvSort32,
      bv::bvnum(0xa345ff22, 32,
                efac)); // only has a const array (not wrapped with STORE)

  kvList.push_back(KeyValue(mkTerm<std::string>("*", efac),
                            mkTerm<mpz_class>(0xa345ff22, efac)));

  llvm::errs() << "Expression: " << *e << "\n";

  HexDump hd2(e);

  llvm::errs() << hd2;

  outcome = boost::lexical_cast<std::string>(hd2);
  outcome = std::regex_replace(outcome, std::regex(" *\n *"), "");

  expected = "*: a3 45 ff 22  |.E.\"|";

  CHECK(outcome == expected);
  checkPairs(kvList.cbegin(), kvList.cend(), hd2.cbegin(), hd2.cend());

  //-----

  ExprVector keys;
  keys.push_back(mkTerm<mpz_class>(0, efac));

  ExprVector values;
  values.push_back(mkTerm<mpz_class>(0x12, efac));

  e = finite_map::constFiniteMap(
      keys, values); // only has a const finite map (not wrapped in SET)

  llvm::errs() << "Expression: " << *e << "\n";
  HexDump hd3(e);

  llvm::errs() << hd3;

  outcome = boost::lexical_cast<std::string>(hd3);
  outcome = std::regex_replace(outcome, std::regex(" *\n *"), "");

  expected = "00: 12  |.|";

  CHECK(outcome == expected);

  kvList.clear();
  kvList.push_back(
      KeyValue(mkTerm<mpz_class>(0, efac), mkTerm<mpz_class>(0x12, efac)));

  checkPairs(kvList.cbegin(), kvList.cend(), hd3.cbegin(), hd3.cend());

  //-----------

  e = array::constArray(bvSort32, intConst); // values are not numerical
  e = array::store(e, bv::bvnum(0, 32, efac), intConst2);
  e = array::store(e, bv::bvnum(4, 32, efac), intConst3);

  llvm::errs() << "Expression: " << *e << "\n";
  HexDump hd4(e);

  llvm::errs() << hd4;

  kvList.clear();
  kvList.push_back(KeyValue(bv::bvnum(0, 32, efac), intConst2));
  kvList.push_back(KeyValue(bv::bvnum(1, 32, efac), intConst, true));
  kvList.push_back(KeyValue(bv::bvnum(4, 32, efac), intConst3));

  checkPairs(kvList.cbegin(), kvList.cend(), hd4.cbegin(), hd4.cend());

  //----------

  e = array::constArray(
      intSort, bv::bvnum(0x1234, 32, efac)); // indices are not numerical
  e = array::store(e, intConst3, bv::bvnum(0x43, 32, efac));
  e = array::store(e, intConst2, bv::bvnum(0xa, 32, efac));

  llvm::errs() << "Expression: " << *e << "\n";
  HexDump hd5(e);

  llvm::errs() << hd5;

  // note: indices are sorted alphanumerically. Indices are not numeric so no
  // gaps are filled in
  kvList.clear();
  kvList.push_back(KeyValue(intConst2, bv::bvnum(0xa, 32, efac)));
  kvList.push_back(KeyValue(intConst3, bv::bvnum(0x43, 32, efac)));

  checkPairs(kvList.cbegin(), kvList.cend(), hd5.cbegin(), hd5.cend());
}
