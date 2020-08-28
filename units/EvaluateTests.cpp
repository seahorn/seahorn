
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#include "doctest.h"

#include <string>

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprGmp.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpArray.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/ExprOpBv.hh"

#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Expr/Smt/Z3.hh"

#include "seahorn/Expr/EvalModel.hh"
#include "seahorn/Expr/Evaluate.hh"

#include "seahorn/Support/SeaDebug.h"

using namespace expr;
using namespace expr::eval;
using namespace seahorn;

Expr boolConst(const std::string &n, ExprFactory &efac) {
  return bind::boolConst(mkTerm<std::string>(n, efac));
}

Expr intConst(const std::string &n, ExprFactory &efac) {
  return bind::intConst(mkTerm<std::string>(n, efac));
}

Expr bvConst(const std::string &n, ExprFactory &efac, unsigned width) {
  return bv::bvConst(mkTerm<std::string>(n, efac), width);
}

template <typename T> void print(T a) { llvm::errs() << a << "\n"; }

template <> void print<mpz_class>(mpz_class a) {
  llvm::errs() << a.to_string() << "\n";
}

template <typename T> void check(ExprVector e, std::vector<T> expected) {

  for (int i = 0; i < e.size(); i++) {
    EvalModelRand<T> evalModel;

    Evaluate<T> eval(&evalModel);

    llvm::errs() << "Expression: " << *e[i] << "\n";
    T result = eval.evaluate(e[i]);

    llvm::errs() << "Expected: ";
    print<T>(expected[i]);
    llvm::errs() << "Actual: ";
    print<T>(result);
    llvm::errs() << "\n";

    CHECK(result == expected[i]);
  }
}

template <typename T>
void check(ExprVector e, std::vector<T> expected, EvalModel<T> &evalModel) {

  for (int i = 0; i < e.size(); i++) {
    Evaluate<T> eval(&evalModel);

    llvm::errs() << "Expression: " << *e[i] << "\n";
    T result = eval.evaluate(e[i]);

    llvm::errs() << "Expected: ";
    print<T>(expected[i]);
    llvm::errs() << "Actual: ";
    print<T>(result);
    llvm::errs() << "\n";

    CHECK(result == expected[i]);
  }
}

TEST_CASE("bvNumBitwise.test") {
  seahorn::SeaEnableLog("ev");
  ExprFactory efac;

  Expr aInt = intConst("aInt", efac);

  Expr aBv = bvConst("aBv", efac, 16);
  Expr bBv = bvConst("bBv", efac, 16);

  Expr bvSort = bv::bvsort(16, efac);

  ExprVector e;
  std::vector<mpz_class> expectedResults;
  Expr temp;

  temp = mk<BNOT>(bv::bvnum(5, 10, efac));
  e.push_back(temp);
  expectedResults.push_back(1018);

  temp = mk<BAND>(bv::bvnum(0xa1, 32, efac), bv::bvnum(1, 32, efac));
  e.push_back(temp);
  expectedResults.push_back(1);

  temp = mk<BOR>(bv::bvnum(0x14bf, 16, efac), bv::bvnum(0xa153, 16, efac));
  e.push_back(temp);
  expectedResults.push_back(0xb5ff);

  temp = mk<BXOR>(bv::bvnum(0xa098, 16, efac), bv::bvnum(0xbb56, 16, efac));
  e.push_back(temp);
  expectedResults.push_back(0x1bce);

  check<mpz_class>(e, expectedResults);
}
TEST_CASE("logicalBool.test") {
  seahorn::SeaEnableLog("ev");
  ExprFactory efac;

  Expr aInt = intConst("aInt", efac);

  Expr aBv = bvConst("aBv", efac, 16);
  Expr bBv = bvConst("bBv", efac, 16);

  Expr bvSort = bv::bvsort(16, efac);

  Expr t = mk<TRUE>(efac);
  Expr f = mk<FALSE>(efac);

  ExprVector e;
  std::vector<mpz_class> expectedResults;
  Expr temp;

  temp = mk<NEG>(t);
  e.push_back(temp);
  expectedResults.push_back(0);

  temp = mk<AND>(t, f);
  e.push_back(temp);
  expectedResults.push_back(0);

  temp = mk<OR>(
      f, mk<EQ>(bv::bvnum(0xb5ff, 16, efac), bv::bvnum(0xb5ff, 16, efac)));
  e.push_back(temp);
  expectedResults.push_back(1);

  temp = mk<BXOR>(t, f);
  e.push_back(temp);
  expectedResults.push_back(1);

  check<mpz_class>(e, expectedResults);
}
TEST_CASE("bvNumArithmetic.test") {
  seahorn::SeaEnableLog("ev");
  ExprFactory efac;

  Expr aInt = intConst("aInt", efac);

  Expr aBv = bvConst("aBv", efac, 16);
  Expr bBv = bvConst("bBv", efac, 16);

  Expr bvSort = bv::bvsort(16, efac);

  ExprVector e;
  std::vector<mpz_class> expectedResults;
  Expr temp;

  temp = mk<BADD>(bv::bvnum(26, 32, efac), bv::bvnum(13, 32, efac));
  e.push_back(temp);
  expectedResults.push_back(39);

  temp = mk<BADD>(bv::bvnum(0xffffffff, 32, efac),
                  bv::bvnum(2, 32, efac)); // overflow
  e.push_back(temp);
  expectedResults.push_back(1);

  temp = mk<BSUB>(bv::bvnum(70, 32, efac), bv::bvnum(70, 32, efac));
  e.push_back(temp);
  expectedResults.push_back(0);

  temp = mk<BSUB>(bv::bvnum(0x1, 8, efac), bv::bvnum(0x2, 8,
                                                     efac)); // overflow
  e.push_back(temp);
  expectedResults.push_back(0xff);

  temp = mk<BMUL>(bv::bvnum(3, 32, efac), bv::bvnum(21, 32, efac));
  e.push_back(temp);
  expectedResults.push_back(63);

  temp = mk<BMUL>(bv::bvnum(50, 8, efac), bv::bvnum(6, 8, efac)); // overflow
  e.push_back(temp);
  expectedResults.push_back(0x2c);

  check<mpz_class>(e, expectedResults);
}
TEST_CASE("bvGeneral.test") {
  seahorn::SeaEnableLog("ev");
  ExprFactory efac;

  Expr aInt = intConst("aInt", efac);
  Expr aBool = boolConst("aBool", efac);

  Expr aBv = bvConst("aBv", efac, 16);
  Expr bBv = bvConst("bBv", efac, 16);

  Expr bvSort = bv::bvsort(16, efac);
  Expr t = mk<TRUE>(efac);
  Expr f = mk<FALSE>(efac);

  ExprVector e;
  std::vector<mpz_class> expectedResults;
  Expr temp;

  temp = bv::concat(bv::bvnum(0xabcd, 16, efac), bv::bvnum(0xef01, 16, efac));
  e.push_back(temp);
  expectedResults.push_back(0xabcdef01);

  temp = bv::extract(7, 4, bv::bvnum(0x3456, 16, efac));
  e.push_back(temp);
  expectedResults.push_back(5);

  temp = bv::sext(bv::bvnum(0x12, 16, efac), 16);
  e.push_back(temp);
  expectedResults.push_back(0xfffffff2);

  temp = bv::sext(bv::bvnum(0xaa, 8, efac), 8);
  e.push_back(temp);
  expectedResults.push_back(0xffaa);

  temp = bv::zext(bv::bvnum(0xfd, 8, efac), 8);
  e.push_back(temp);
  expectedResults.push_back(0xfd);

  temp = mk<EQ>(bv::bvnum(0xa, 16, efac), bv::bvnum(0xa1, 16, efac));
  e.push_back(temp);
  expectedResults.push_back(0);

  temp = mk<NEQ>(bv::bvnum(0xa, 16, efac), bv::bvnum(0xa, 16, efac));
  e.push_back(temp);
  expectedResults.push_back(0);

  temp = mk<BULT>(bv::bvnum(0xa6, 32, efac), bv::bvnum(0x8, 32, efac));
  e.push_back(temp);
  expectedResults.push_back(0);

  temp = mk<BULE>(bv::bvnum(0xbbff, 32, efac), bv::bvnum(0xbbff, 32, efac));
  e.push_back(temp);
  expectedResults.push_back(1);

  temp = mk<BUGT>(bv::bvnum(0x1, 32, efac), bv::bvnum(0xbbbbaaaaaa, 32, efac));
  e.push_back(temp);
  expectedResults.push_back(0);

  temp = mk<BUGT>(bv::bvnum(0x1, 32, efac), bv::bvnum(0x2, 32, efac));
  e.push_back(temp);
  expectedResults.push_back(0);

  temp = mk<BSLT>(bv::bvnum(0xa6, 8, efac),
                  bv::bvnum(0x2, 8, efac)); // 0xa6 negative
  e.push_back(temp);
  expectedResults.push_back(1);

  temp = mk<BSLT>(bv::bvnum(0x2, 8, efac), bv::bvnum(0xa6, 8, efac));
  e.push_back(temp);
  expectedResults.push_back(0);

  temp = mk<BSLT>(bv::bvnum(0xff, 8, efac), bv::bvnum(0xa6, 8, efac));
  e.push_back(temp);
  expectedResults.push_back(1);

  temp = mk<BSLE>(bv::bvnum(0xff, 8, efac), bv::bvnum(0xa6, 8, efac));
  e.push_back(temp);
  expectedResults.push_back(1);

  temp = mk<BSLE>(bv::bvnum(0x01, 8, efac), bv::bvnum(0x01, 8, efac));
  e.push_back(temp);
  expectedResults.push_back(1);

  temp = mk<BSGT>(bv::bvnum(0xffff, 16, efac), bv::bvnum(0x01, 16, efac));
  e.push_back(temp);
  expectedResults.push_back(0);

  temp = mk<BSGE>(bv::bvnum(0xffff, 16, efac), bv::bvnum(0xff01, 16, efac));
  e.push_back(temp);
  expectedResults.push_back(0);

  temp = bv::bvnum(-4, 16, efac); // result should be the 2s complement
  e.push_back(temp);
  expectedResults.push_back(0xfffc);

  temp = bv::bvnum(-7, 10, efac); // result should be the 2s complement
  e.push_back(temp);
  expectedResults.push_back(0x3f9);

  check<mpz_class>(e, expectedResults);
}

TEST_CASE("ite.test") {
  seahorn::SeaEnableLog("ev");
  ExprFactory efac;

  Expr aInt = intConst("aInt", efac);
  Expr aBool = boolConst("aBool", efac);

  Expr aBv = bvConst("aBv", efac, 16);
  Expr bBv = bvConst("bBv", efac, 16);

  Expr bvSort = bv::bvsort(16, efac);
  Expr t = mk<TRUE>(efac);
  Expr f = mk<FALSE>(efac);

  ExprVector e;
  std::vector<uint64_t> expectedResults;
  Expr temp;

  temp = mk<ITE>(mk<NEQ>(t, t), bv::bvnum(0x14, 8, efac),
                 bv::bvnum(0x22, 8, efac));
  e.push_back(temp);
  expectedResults.push_back(0x22);

  temp = mk<ITE>(mk<NEQ>(f, t), bv::bvnum(0x14, 8, efac),
                 bv::bvnum(0x22, 8, efac));
  e.push_back(temp);
  expectedResults.push_back(0x14);

  temp = mk<ITE>(
      f, bv::bvnum(0x14, 64, efac),
      mk<ITE>(t, mk<BSUB>(bv::bvnum(0x65, 64, efac), bv::bvnum(0x2, 64, efac)),
              bv::bvnum(0xabcd, 64, efac)));
  e.push_back(temp);
  expectedResults.push_back(0x63);

  check<uint64_t>(e, expectedResults);
}

TEST_CASE("lambda.test") {
  seahorn::SeaEnableLog("ev");
  ExprFactory efac;

  Expr aBool = boolConst("aBool", efac);

  Expr aBv = bvConst("aBv", efac, 16);
  Expr bBv = bvConst("bBv", efac, 32);

  Expr boolSort = sort::boolTy(efac);
  Expr bvSort16 = bv::bvsort(16, efac);
  Expr bvSort32 = bv::bvsort(32, efac);

  Expr bvarBound0 = bind::bvar(0, boolSort);

  Expr t = mk<TRUE>(efac);
  Expr f = mk<FALSE>(efac);

  ExprVector e;
  std::vector<uint16_t> expectedResults;
  Expr temp;
  Expr body;

  body = mk<BMUL>(bv::bvnum(4, 16, efac), bv::bvnum(10, 16, efac));
  temp = mk<LAMBDA>(aBv, body);
  e.push_back(temp);
  expectedResults.push_back(40);

  check<uint16_t>(e, expectedResults);
  e.clear();
  expectedResults.clear();

  //---------

  std::vector<uint32_t> expectedResults32;

  body = mk<ITE>(mk<EQ>(bvarBound0, bv::bvnum(0x8048014, 32, efac)),
                 bv::bvnum(0x2e6d6f63, 32, efac), bv::bvnum(0, 32, efac));
  temp = mk<LAMBDA>(bBv, body);
  e.push_back(temp);
  expectedResults32.push_back(0x2e6d6f63);

  EvalModelRand<uint32_t> evalModel(1);
  evalModel.newLambda(temp);
  evalModel.setBoundValue(temp, bvarBound0, BvNum<uint32_t>(0x8048014, 32));

  check<uint32_t>(e, expectedResults32, evalModel);

  expectedResults32.clear();

  expectedResults32.push_back(0);
  evalModel.setBoundValue(temp, bvarBound0, BvNum<uint32_t>(0x1234, 32));

  check<uint32_t>(e, expectedResults32, evalModel);
  e.clear();
  expectedResults32.clear();

  //---------

  Expr lambda = mk<LAMBDA>(bBv, mk<BADD>(bvarBound0, bv::bvnum(10, 32, efac)));
  Expr lambda2 =
      mk<LAMBDA>(bBv, mk<BOR>(bvarBound0, bv::bvnum(0x81, 32, efac)));

  EvalModelRand<uint32_t> evalModel2(1);

  evalModel2.newLambda(lambda);
  evalModel2.setBoundValue(lambda, bvarBound0, BvNum<uint32_t>(0x1111, 32));

  evalModel2.newLambda(lambda2);
  evalModel2.setBoundValue(
      lambda2, bvarBound0,
      BvNum<uint32_t>(0xff, 32)); // same bound as lambda 1, but different scope

  temp = mk<BADD>(lambda, lambda2);
  e.push_back(temp);
  expectedResults32.push_back(0x121a);
  // (0x1111 + 10) + (0xff | 0x81) = 0x111b + 0xff = 0x121a

  check<uint32_t>(e, expectedResults32, evalModel2);
}

TEST_CASE("array.test") {
  seahorn::SeaEnableLog("ev");
  ExprFactory efac;

  Expr bvSort = bv::bvsort(32, efac);
  Expr arraySort = sort::arrayTy(bvSort, bvSort);

  Expr aInt = intConst("aInt", efac);

  Expr arr = bind::mkConst(mkTerm<std::string>("aAr", efac), arraySort);

  ExprVector e;
  std::vector<mpz_class> expectedResults;
  Expr temp;

  temp = op::array::store(arr, bv::bvnum(2, 32, efac), bv::bvnum(90, 32, efac));
  temp =
      op::array::store(temp, bv::bvnum(8, 32, efac), bv::bvnum(100, 32, efac));
  temp = op::array::select(temp, bv::bvnum(2, 32, efac));
  e.push_back(temp);
  expectedResults.push_back(90);

  temp = op::array::constArray(bvSort, bv::bvnum(10, 32, efac));
  temp =
      op::array::store(temp, bv::bvnum(1, 32, efac), bv::bvnum(21, 32, efac));
  temp =
      op::array::store(temp, bv::bvnum(2, 32, efac), bv::bvnum(11, 32, efac));
  temp = op::array::select(temp, bv::bvnum(5, 32, efac));
  e.push_back(temp);
  expectedResults.push_back(10);

  check<mpz_class>(e, expectedResults);
}
TEST_CASE("EvalModelRandArray.test") {
  seahorn::SeaEnableLog("ev");
  ExprFactory efac;

  Expr bvSort = bv::bvsort(32, efac);
  Expr arraySort = sort::arrayTy(bvSort, bvSort);

  Expr arr = bind::mkConst(mkTerm<std::string>("aAr", efac), arraySort);

  EvalModelRand<mpz_class> evalModel(1);

  evalModel.newArray(arr);

  evalModel.setArrayValue(arr, BvNum<mpz_class>(5, 32),
                          BvNum<mpz_class>(7, 32));
  evalModel.setArrayValue(arr, BvNum<mpz_class>(7, 32),
                          BvNum<mpz_class>(34, 32));
  evalModel.setArrayValue(arr, BvNum<mpz_class>(0, 32),
                          BvNum<mpz_class>(9, 32));
  evalModel.setArrayValue(arr, BvNum<mpz_class>(5, 32),
                          BvNum<mpz_class>(1, 32)); // override previous 5

  BvNum<mpz_class> result =
      evalModel.getArrayValue(arr, BvNum<mpz_class>(5, 32));
  CHECK(result == BvNum<mpz_class>(1, 32));

  result = evalModel.getArrayValue(arr, BvNum<mpz_class>(0, 32));
  CHECK(result == BvNum<mpz_class>(9, 32));

  BvNum<mpz_class> oldResult =
      evalModel.getArrayValue(arr, BvNum<mpz_class>(2, 32));
  result = evalModel.getArrayValue(arr, BvNum<mpz_class>(2, 32));
  CHECK(result == oldResult); // value was randomly generated
  CHECK(result.getWidth() == 32);

  result = evalModel.getArrayValue(arr, BvNum<mpz_class>(7, 32));
  CHECK(result == BvNum<mpz_class>(34, 32));

  //------------

  Expr arr2 = op::array::constArray(bvSort, mk<TRUE>(efac));
  evalModel.newArray(arr2, BvNum<mpz_class>(true));

  evalModel.setArrayValue(arr2, BvNum<mpz_class>(9, 32),
                          BvNum<mpz_class>(false));

  result = evalModel.getArrayValue(arr2, BvNum<mpz_class>(9, 32));
  CHECK(result == BvNum<mpz_class>(false));

  result = evalModel.getArrayValue(arr2, BvNum<mpz_class>(12, 32));
  CHECK(result == BvNum<mpz_class>(true));
}

TEST_CASE("EvalModelRandLambda.test") {
  seahorn::SeaEnableLog("ev");
  ExprFactory efac;

  Expr boolSort = sort::boolTy(efac);
  Expr t = mk<TRUE>(efac);
  Expr f = mk<FALSE>(efac);

  Expr bvSort = bv::bvsort(32, efac);

  Expr aBv = bvConst("aBv", efac, 32);
  Expr bBv = bvConst("bBv", efac, 32);

  Expr bound0 = bind::bvar(0, bvSort);
  Expr bound1 = bind::bvar(1, bvSort);

  Expr body = bound0;

  Expr lambda = mk<LAMBDA>(aBv, body);

  EvalModelRand<mpz_class> evalModel(1);

  evalModel.newLambda(lambda);

  evalModel.setBoundValue(lambda, bound0, BvNum<mpz_class>(9, 32));

  BvNum<mpz_class> result = evalModel.getBoundValue(lambda, bound0);
  CHECK(result == BvNum<mpz_class>(9, 32));

  // //------------

  Expr lambda2 = mk<LAMBDA>(aBv, bBv, body);

  evalModel.newLambda(lambda2);

  evalModel.setBoundValue(lambda2, bound0, BvNum<mpz_class>(0, 32));

  result = evalModel.getBoundValue(lambda2, bound0);
  CHECK(result == BvNum<mpz_class>(0, 32));

  result = evalModel.getBoundValue(lambda, bound0);
  CHECK(result ==
        BvNum<mpz_class>(
            9, 32)); // previous lambda should not be affect by this one

  // //------------

  BvNum<mpz_class> oldResult =
      evalModel.getBoundValue(lambda2, bound1); // randomly generated
  result = evalModel.getBoundValue(lambda2, bound1);
  CHECK(result == oldResult);
}
