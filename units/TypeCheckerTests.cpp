/**==-- Type Checker Tests --==*/
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#include "doctest.h"

#include "boost/lexical_cast.hpp"

#include "llvm/ADT/APInt.h"
#include "llvm/Support/raw_ostream.h"

#include <string>

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprGmp.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/ExprOpBv.hh"
#include "seahorn/Expr/TypeChecker.hh"

#include "seahorn/Support/SeaDebug.h"

using namespace expr;
using namespace llvm;

Expr boolConst(const std::string &n, ExprFactory &efac) {
  return bind::boolConst(mkTerm<std::string>(n, efac));
}

Expr intConst(const std::string &n, ExprFactory &efac) {
  return bind::intConst(mkTerm<std::string>(n, efac));
}

Expr realConst(const std::string &n, ExprFactory &efac) {
  return bind::realConst(mkTerm<std::string>(n, efac));
}

Expr unintConst(const std::string &n, ExprFactory &efac) {
  return bind::unintConst(mkTerm<std::string>(n, efac));
}

Expr bvConst(const std::string &n, ExprFactory &efac, unsigned width) {
  return bv::bvConst(mkTerm<std::string>(n, efac), width);
}

void checkNotWellFormed(std::vector<Expr> e, std::vector<Expr> error) {
  Expr errorSort = sort::errorTy(e[0]->efac());
  TypeChecker tc;

  for (int i = 0; i < e.size(); i++) {
    llvm::errs() << "Expression: " << *e[i] << "\n";
    Expr ty = tc.typeOf(e[i]);

    CHECK(ty == errorSort);
    CHECK(tc.getErrorExp() == error[i]);
    if (ty)
      llvm::errs() << "Type is " << *ty << "\n\n";
    else
      llvm::errs() << "Not well-formed expression. Type inference failed\n";
  }
}

void checkWellFormed(std::vector<Expr> e, Expr type) {
  TypeChecker tc;

  for (int i = 0; i < e.size(); i++) {
    llvm::errs() << "Expression: " << *e[i] << "\n";
    Expr ty = tc.typeOf(e[i]);

    CHECK(ty == type);
    if (ty)
      llvm::errs() << "Type is " << *ty << "\n\n";
    else
      llvm::errs() << "Not well-formed expression. Type inference failed\n";
  }
}

TEST_CASE("typeOf.test") {
  // enable LOG("tc", ...) code
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr x = boolConst("x", efac);
  Expr y = boolConst("y", efac);
  Expr z = boolConst("z", efac);

  // -- we use 'type' and 'sort' interchangeably
  Expr boolSort = sort::boolTy(efac);

  // x is boolean
  CHECK(bind::typeOf(x) == boolSort);

  Expr e = boolop::land(x, y);
  llvm::errs() << *e << "\n";
  // -- un-comment
  // -- fails with assertion failure inside typeOf()
  // CHECK(bind::typeOf(e) == boolSort);

  e = boolop::lor(x, e);

  TypeChecker tc;
  Expr ty = tc.typeOf(e);

  CHECK(ty == boolSort);
  if (ty)
    llvm::errs() << "Type is " << *ty << "\n";
  else
    llvm::errs() << "Not well-formed expression. Type inference failed\n";
}

TEST_CASE("boolWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr x = boolConst("x", efac);
  Expr y = boolConst("y", efac);
  Expr z = boolConst("z", efac);

  Expr aInt = intConst("aInt", efac);

  Expr boolSort = sort::boolTy(efac);
  Expr intSort = sort::intTy(efac);

  std::vector<Expr> e;
  Expr temp;

  // (!x && y)|| (x || z)
  temp = boolop::land(boolop::lneg(x), y);
  e.push_back(temp);
  temp = boolop::lor(e[0], boolop::lor(x, z));
  e.push_back(temp);

  //!(x -> y) && z
  temp = boolop::lneg(boolop::limp(x, y));
  e.push_back(temp);
  temp = boolop::land(e[1], z);
  e.push_back(temp);

  // ((!x && y)|| (x || z)) <-> (!(x -> y) && z )
  temp = mk<IFF>(e[0], e[1]);
  e.push_back(temp);

  temp = mk<ITE>(y, x, mk<XOR>(x, y));
  e.push_back(temp);

  temp = boolop::limp(mk<TRUE>(efac), mk<FALSE>(efac));
  e.push_back(temp);

  checkWellFormed(e, boolSort);
  e.clear();

  temp = mk<ITE>(y, x, aInt);

  checkWellFormed(e, intSort);

}
TEST_CASE("notWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  ExprFactory efac;

  Expr xInt = intConst("intX", efac); // variable of type int

  Expr yBool = boolConst("yBool", efac);
  Expr aBool = boolConst("aBool", efac);
  Expr zBool = boolConst("zBool", efac);

  Expr errorSort = sort::errorTy(efac);

  std::vector<Expr> e;
  Expr temp;
  std::vector<Expr> error;
  Expr tempError;

  // yBool && (zBool && xInt)
  tempError = boolop::land(zBool, xInt);
  error.push_back(tempError);
  temp = boolop::land(yBool, error.back());
  e.push_back(temp);

  // (yBool -> zBool) -> !xInt
  tempError = boolop::lneg(xInt);
  error.push_back(tempError);
  temp = boolop::limp(boolop::limp(yBool, zBool), error.back());
  e.push_back(temp);

  // (zBool || xInt ) && (yBool -> zBool)
  tempError = boolop::lor(zBool, xInt);
  error.push_back(tempError);
  temp = boolop::land(error.back(), boolop::limp(yBool, zBool));
  e.push_back(temp);

  checkNotWellFormed(e, error);
}

TEST_CASE("intWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr x = intConst("x", efac);
  Expr y = intConst("y", efac);
  Expr z = intConst("z", efac);

  Expr intSort = sort::intTy(efac);

  std::vector<Expr> e;
  Expr temp;

  temp = mk<PLUS>(x, y, z);
  e.push_back(temp);

  temp = mk<PLUS>(mk<MINUS>(x, y), y, z);
  e.push_back(temp);

  TypeChecker tc;

  checkWellFormed(e, intSort);
}

TEST_CASE("realWellFormed.test") {

  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr aReal = realConst("aReal", efac);
  Expr bReal = realConst("bReal", efac);
  Expr cReal = realConst("cReal", efac);

  Expr realSort = sort::realTy(efac);

  TypeChecker tc;

  std::vector<Expr> e;
  Expr temp;

  //(aReal / bReal) * aReal * (aReal - bReal)
  temp = mk<MULT>(mk<DIV>(aReal, bReal), aReal, mk<UN_MINUS>(aReal, bReal));
  e.push_back(temp);

  // abs ((aReal / bReal) * aReal * (aReal - bReal)) % cReal
  temp = mk<REM>(mk<ABS>(e[0]), aReal);
  e.push_back(temp);

  checkWellFormed(e, realSort);
}

TEST_CASE("unintWellFormed.test") {

  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr aUnint = unintConst("aUnint", efac);
  Expr bUnint = unintConst("bUnint", efac);
  Expr cUnint = unintConst("cUnint", efac);

  Expr unintSort = sort::unintTy(efac);

  TypeChecker tc;

  std::vector<Expr> e;
  Expr temp;

  // aUnint mod (bUnint / cUnint)
  temp = mk<MOD>(aUnint, mk<IDIV>(bUnint, cUnint));
  e.push_back(temp);

  //  aUnint - (aUnint * cUnint) - (aUnint * cUnint)
  temp =
      mk<UN_MINUS>(aUnint, mk<MULT>(aUnint, cUnint), mk<MULT>(aUnint, cUnint));
  e.push_back(temp);

  checkWellFormed(e, unintSort);
}

TEST_CASE("numNotWellFormed.test") {

  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr aInt = intConst("aint", efac);
  Expr bInt = intConst("bInt", efac);
  Expr cReal = realConst("cReal", efac);
  Expr dUnint = unintConst("dUnint", efac);
  Expr eBool = boolConst("eBool", efac);

  std::vector<Expr> e;
  Expr temp;
  std::vector<Expr> error;
  Expr tempError;

  temp = mk<ABS>(eBool);
  e.push_back(temp);
  tempError = e.back();
  error.push_back(tempError);

  temp = mk<ABS>(aInt, bInt);
  e.push_back(temp);
  tempError = e.back();
  error.push_back(tempError);

  temp = mk<DIV>(dUnint, mk<PLUS>(cReal, cReal), mk<MULT>(dUnint, dUnint));
  e.push_back(temp);
  tempError = e.back();
  error.push_back(tempError);

  checkNotWellFormed(e, error);
}
TEST_CASE("compareWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr xInt = intConst("xInt", efac);
  Expr yInt = intConst("yInt", efac);
  Expr zInt = intConst("zInt", efac);

  Expr xReal = realConst("xReal", efac);
  Expr yReal = realConst("yReal", efac);

  Expr xBool = boolConst("xBool", efac);
  Expr yBool = boolConst("yBool", efac);

  Expr boolSort = sort::boolTy(efac);

  std::vector<Expr> e;
  Expr temp;

  // (xBool && yBool && !xBool)= yBool
  temp = mk<EQ>(mk<AND>(xBool, yBool, mk<NEG>(xBool)), yBool);
  e.push_back(temp);

  // ((xInt-yInt)+ yInt) <= abs(zInt)
  temp = mk<LEQ>(mk<PLUS>(mk<MINUS>(xInt, yInt), yInt), mk<ABS>(zInt));
  e.push_back(temp);

  // (xReal >= yReal) != xBool
  temp = mk<NEQ>(mk<GEQ>(xReal, yReal), xBool);
  e.push_back(temp);

  //  (xReal mod yReal ) < xRreal
  temp = mk<LT>(mk<MOD>(xReal, yReal), xReal);
  e.push_back(temp);

  checkWellFormed(e, boolSort);
}
TEST_CASE("compareNotWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr xInt = intConst("xInt", efac);
  Expr yInt = intConst("yInt", efac);
  Expr zInt = intConst("zInt", efac);

  Expr xReal = realConst("xReal", efac);
  Expr yReal = realConst("yReal", efac);

  Expr xBool = boolConst("xBool", efac);
  Expr yBool = boolConst("yBool", efac);

  std::vector<Expr> e;
  Expr temp;
  std::vector<Expr> error;
  Expr tempError;

  tempError = mk<LT>(xBool, yBool);
  error.push_back(tempError);

  // xBool && (xBool < yBool )
  temp = mk<AND>(xBool, error.back());
  e.push_back(temp);

  tempError = mk<GEQ>(xReal, xReal, yReal);
  error.push_back(tempError);

  // yBool != [>=(xReal, xReal, yReal)]
  temp = mk<NEQ>(yBool, error.back());
  e.push_back(temp);

  tempError = mk<EQ>(xReal, xInt);
  error.push_back(tempError);

  // ((xReal == xInt) > xReal )|| yBool
  temp = mk<OR>(mk<GT>(error.back(), xReal), yBool);
  e.push_back(temp);

  tempError = mk<EQ>(mk<IMPL>(xBool, yBool), xReal);
  error.push_back(tempError);

  // (xBool -> yBool ) == xReal
  temp = error.back();
  e.push_back(temp);

  checkNotWellFormed(e, error);
}
TEST_CASE("bvWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr aInt = intConst("aInt", efac);

  Expr bvSort = bv::bvsort(10, efac);
  Expr bvSort5 = bv::bvsort(5, efac);

  Expr a10 = bvConst("a10", efac, 10);
  Expr b10 = bvConst("b10", efac, 10);
  Expr c10 = bvConst("c10", efac, 10);
  // Expr d10 = bv::bvnum(aInt, bvSort); //TODO

  Expr a5 = bvConst("a5", efac, 5);
  Expr b5 = bvConst("b5", efac, 5);
  Expr c5 = bvConst("c5", efac, 5);

  Expr a2 = bvConst("a2", efac, 2);

  Expr a3 = bvConst("a3", efac, 3);

  std::vector<Expr> e;
  Expr temp;

  temp = mk<BNOT>(mk<BOR>(a10, b10));
  e.push_back(temp);

  temp = mk<BAND>(mk<BREDAND>(a10), b10);
  e.push_back(temp);

  temp = mk<BREDOR>(mk<BXNOR>(mk<BNEG>(a10), mk<BOR>(b10, c10)));
  e.push_back(temp);

  temp = mk<BSUB>(mk<BCONCAT>(a5, b5), a10);
  e.push_back(temp);

  temp = mk<BCONCAT>(a5, a3, a2);
  e.push_back(temp);

  temp = mk<BADD>(mk<BNAND>(a10, b10), mk<BSHL>(c10, c10));
  e.push_back(temp);

  temp = mk<BSHL>(bv::sext(a5, 5), a10);
  e.push_back(temp);

  temp = bv::extract(12, 3, mk<BCONCAT>(a10, b5));
  e.push_back(temp);

  temp = bv::zext(bv::extract(5, 1, b10), 5);
  e.push_back(temp);

  temp = mk<BROTATE_LEFT>(mkTerm<unsigned>(5, efac), a10);
  e.push_back(temp);

  temp = mk<BREPEAT>(mkTerm<unsigned>(1, efac),
                     mk<BROTATE_RIGHT>(mkTerm<unsigned>(2, efac), b10));
  e.push_back(temp);

  temp = mk<BREPEAT>(mkTerm<unsigned>(2, efac), a5);
  e.push_back(temp);

  temp = mk<BUGE>(e.back(),
                  mk<BEXT_ROTATE_RIGHT>(mkTerm<unsigned>(2, efac), e.back()));
  e.push_back(temp);

  temp = mk<INT2BV>(mkTerm<unsigned>(10, efac), aInt);
  e.push_back(temp);

  checkWellFormed(e, bvSort);
}
TEST_CASE("bvNotWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr aInt = intConst("aInt", efac);
  Expr aUnint = unintConst("aUnint", efac);
  Expr aReal = realConst("aReal", efac);

  Expr bvSort = bv::bvsort(10, efac);
  Expr bvSort5 = bv::bvsort(5, efac);
  Expr bvSort3 = bv::bvsort(3, efac);

  Expr a10 = bvConst("a10", efac, 10);
  Expr b10 = bvConst("b10", efac, 10);
  Expr c10 = bvConst("c10", efac, 10);

  Expr a7 = bvConst("a7", efac, 7);

  Expr a5 = bvConst("a5", efac, 5);
  Expr b5 = bvConst("b5", efac, 5);
  Expr c5 = bvConst("c5", efac, 5);

  std::vector<Expr> e;
  Expr temp;
  std::vector<Expr> error;
  Expr tempError;

  tempError = mk<BNOT>(a10, a10); // too many arguments: Unary
  error.push_back(tempError);
  temp = error.back();
  e.push_back(temp);

  tempError = mk<BREDAND>(aInt); // wrong type of argument Unary
  error.push_back(tempError);
  temp = mk<BMUL>(mk<BSLE>(error.back(), a10), b10);
  e.push_back(temp);

  tempError = mk<BSDIV>(a10); // not enough arguments Nary
  error.push_back(tempError);
  temp = mk<BSGT>(error.back(), a10);
  e.push_back(temp);

  tempError = mk<BSGT>(a10, aUnint); // wrong type of argument
  error.push_back(tempError);
  temp = mk<BSHL>(b10, error.back());
  e.push_back(temp);

  tempError = mk<BASHR>(a5); // not enough arguments : binary
  error.push_back(tempError);
  temp = error.back();
  e.push_back(temp);

  tempError = mk<BSHL>(a10, b10, c10); // too many arguments : binary
  error.push_back(tempError);
  temp = mk<BNAND>(a10, mk<BREDOR>(error.back()));
  e.push_back(temp);

  tempError = mk<BCONCAT>(a7); // not enough arguments : concat
  error.push_back(tempError);
  temp = error.back(); // mk<BCONCAT>(error[6], a3);
  e.push_back(temp);

  tempError = mk<BCONCAT>(a5, aReal); // wrong type of arugment
  error.push_back(tempError);
  temp = mk<BNOT>(error.back());
  e.push_back(temp);

  tempError = mk<BUGT>(a10, mk<BCONCAT>(a5, a10)); // widths do not match
  error.push_back(tempError);
  temp = error.back();
  e.push_back(temp);

  tempError = mk<BSEXT>(a10, b10); // should be {bv, bvsort}
  error.push_back(tempError);
  temp = mk<BCONCAT>(error.back(), a5);
  e.push_back(temp);

  tempError = mk<BSEXT>(a10, bvSort, b10);
  error.push_back(tempError);
  temp = error.back();
  e.push_back(temp);

  tempError = bv::extract(5, 9, a10); // high is lower than low
  error.push_back(tempError);
  temp = mk<BUREM>(mk<BNEG>(a5), b5, error.back());
  e.push_back(temp);

  tempError = bv::extract(6, 4, c5); // high is higher than width
  error.push_back(tempError);
  temp = error.back();
  e.push_back(temp);

  std::vector<Expr> args;
  args.push_back(mkTerm<unsigned>(9, efac));
  args.push_back(mkTerm<unsigned>(8, efac));
  args.push_back(mkTerm<unsigned>(0, efac));
  args.push_back(a10);
  tempError =
      mknary<BEXTRACT>(args.rbegin(), args.rend()); // too many arguemtns
  error.push_back(tempError);
  temp = bv::sext(error.back(), 8);
  e.push_back(temp);

  tempError =
      mk<BEXTRACT>(mkTerm<std::string>("5", efac), mkTerm<unsigned>(1, efac),
                   a10); // wrong type of argument
  error.push_back(tempError);
  temp = error.back();
  e.push_back(temp);

  tempError = bv::extract(3, 1, aInt); // wrong type of argument
  error.push_back(tempError);
  temp = mk<BXNOR>(mk<BCONCAT>(a7, error.back()), b10);
  e.push_back(temp);

  tempError =
      mk<BROTATE_LEFT>(mkTerm<unsigned>(11, efac)); // not enough arguments
  error.push_back(tempError);
  temp = mk<BXOR>(mk<BNOT>(error.back()), error.back());
  e.push_back(temp);

  Expr uintA = mkTerm<unsigned>(5, efac);
  Expr uintB = mkTerm<unsigned>(7, efac);
  tempError = mk<BSHL>(mk<BREPEAT>(uintA, a5),
                       mk<BEXT_ROTATE_RIGHT>(uintB, a7)); // mismatching widths
  error.push_back(tempError);
  temp = error.back();
  e.push_back(temp);

  tempError = mk<BOR>(mk<INT2BV>(mkTerm<unsigned>(7, efac), aInt),
                      b5); // mismatching widths
  error.push_back(tempError);
  temp = mk<BCONCAT>(error.back(), error.back());
  e.push_back(temp);

  tempError = mk <BSGT>(a10, b10, c10); // too many arguments
  error.push_back(tempError);
  e.push_back(tempError);

  checkNotWellFormed(e, error);
}
TEST_CASE("bvDifReturnTypeWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr bvSort = bv::bvsort(10, efac);
  Expr boolSort = sort::boolTy(efac);
  Expr intSort = sort::intTy(efac);

  Expr a10 = bvConst("a10", efac, 10);
  Expr b10 = bvConst("b10", efac, 10);
  Expr c10 = bvConst("c10", efac, 10);

  Expr a8 = bvConst("a8", efac, 8);

  Expr aBool = boolConst("aBool", efac);
  Expr aInt = intConst("aInt", efac);

  Expr temp;
  std::vector<Expr> e;

  temp = mk<SADD_NO_OVERFLOW>(a10, b10);
  e.push_back(temp);

  temp = mk<AND>(mk<UADD_NO_OVERFLOW>(a10, b10), aBool);
  e.push_back(temp);

  temp = mk<SSUB_NO_UNDERFLOW>(a10, mk<BASHR>(b10, c10));
  e.push_back(temp);

  temp = mk<UMUL_NO_OVERFLOW>(bv::zext(a8, 2), mk<BSUB>(b10, c10));
  e.push_back(temp);

  checkWellFormed(e, boolSort);

  int size2 = 3;
  std::vector<Expr> e2;

  temp = mk<BV2INT>(a10);
  e2.push_back(temp);

  temp = mk<BV2INT>(mk<BSLE>(a10, b10));
  e2.push_back(temp);

  temp = mk<PLUS>(mk<BV2INT>(mk<BUREM>(a10, b10)), aInt);
  e2.push_back(temp);

  checkWellFormed(e2, intSort);
}
TEST_CASE("bvDifReturnTypeNotWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;
  Expr bvSort = bv::bvsort(10, efac);
  Expr boolSort = sort::boolTy(efac);
  Expr intSort = sort::intTy(efac);

  Expr aInt = intConst("aInt", efac);
  Expr bInt = intConst("bInt", efac);

  Expr a10 = bvConst("a10", efac, 10);
  Expr b10 = bvConst("b10", efac, 10);
  Expr c10 = bvConst("c10", efac, 10);

  Expr a5 = bvConst("a5", efac, 5);

  std::vector<Expr> e;
  Expr temp;
  std::vector<Expr> error;
  Expr tempError;

  tempError = mk<SMUL_NO_OVERFLOW>(a5); // not enough arguments
  error.push_back(tempError);
  temp = mk<NEG>(error.back());
  e.push_back(temp);

  tempError = mk<SMUL_NO_UNDERFLOW>(mk<BV2INT>(a10), aInt); // wrong type
  error.push_back(tempError);
  temp = error.back();
  e.push_back(temp);

  tempError = mk<BV2INT>(c10, b10); // too many arguments
  error.push_back(tempError);
  temp = mk<NEQ>(error.back(), mk<BV2INT>(a10));
  e.push_back(temp);

  tempError = mk<BV2INT>(aInt); // wrong type
  error.push_back(tempError);
  temp = mk<REM>(mk<ABS>(error.back(), bInt));
  e.push_back(temp);

  checkNotWellFormed(e, error);
}
TEST_CASE("variantWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  ExprFactory efac;

  Expr anySort = sort::anyTy(efac);

  Expr aInt = intConst("aInt", efac);
  Expr bInt = intConst("bInt", efac);

  Expr a10 = bvConst("a10", efac, 10);
  Expr b10 = bvConst("b10", efac, 10);
  Expr c10 = bvConst("c10", efac, 10);

  std::vector<Expr> e;
  Expr temp;

  temp = variant::variant(0, aInt);
  e.push_back(temp);

  temp = variant::variant(1, mk<MULT>(aInt, bInt));
  e.push_back(temp);

  temp = variant::tag(aInt, mk<BNEG>(a10));
  e.push_back(temp);

  checkWellFormed(e, anySort);
}
TEST_CASE("variantNotWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr bvSort = bv::bvsort(10, efac);
  Expr boolSort = sort::boolTy(efac);
  Expr intSort = sort::intTy(efac);

  Expr aInt = intConst("aInt", efac);
  Expr bInt = intConst("bInt", efac);

  Expr aBool = boolConst("aBool", efac);

  Expr a10 = bvConst("a10", efac, 10);
  Expr b10 = bvConst("b10", efac, 10);
  Expr c10 = bvConst("c10", efac, 10);

  std::vector<Expr> e;
  Expr temp;
  std::vector<Expr> error;
  Expr tempError;

  tempError = mk<VARIANT>(mkTerm<unsigned>(5, efac), aBool, aInt);
  error.push_back(tempError);
  temp = mk<PLUS>(mk<ABS>(error.back()), mk<PLUS>(aInt, error.back()));
  e.push_back(temp);

  tempError = mk <TAG> (aInt, bInt , bInt);
  error.push_back(tempError);
  temp = error.back();
  e.push_back(temp);

  checkNotWellFormed(e, error);
}
TEST_CASE("arrayWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  ExprFactory efac;

  Expr intSort = sort::intTy(efac);
  Expr boolSort = sort::boolTy(efac);
  Expr arraySort1 = sort::arrayTy(intSort, intSort);

  Expr aInt = intConst("aInt", efac);
  Expr bInt = intConst("bInt", efac);

  Expr aBool = boolConst("aBool", efac);
  Expr bBool = boolConst("bBool", efac);

  Expr aAr = bind::mkConst(mkTerm<std::string>("aAr", efac), arraySort1);

  std::vector<Expr> e;
  Expr temp;

  temp = array::select(aAr, aInt);
  e.push_back(temp);

  temp = mk<ABS>(array::select(aAr, mk<PLUS>(bInt, aInt)));
  e.push_back(temp);

  temp = array::aDefault(aAr);
  e.push_back(temp);

  temp = array::aDefault(array::constArray(intSort, bInt));
  e.push_back(temp);

  checkWellFormed(e, intSort);
  e.clear();

  Expr arraySort2 = sort::arrayTy(intSort, boolSort);
  Expr aAr2 = bind::mkConst(mkTerm<std::string>("aAr", efac), arraySort2);

  temp = array::store(aAr2, aInt, aBool);
  e.push_back(temp);

  temp = array::store(aAr2, mk<PLUS>(aInt, bInt), mk<NEQ>(aBool, bBool));
  e.push_back(temp);

  checkWellFormed(e, arraySort2);
  e.clear();

  temp = array::constArray(intSort, aBool);
  e.push_back(temp);

  temp = array::store(array::constArray(intSort, aBool), aInt, aBool);
  e.push_back(temp);

  checkWellFormed(e, arraySort2);
  e.clear();
}
TEST_CASE("arrayNotWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  ExprFactory efac;

  Expr intSort = sort::intTy(efac);
  Expr boolSort = sort::boolTy(efac);
  Expr arraySort1 = sort::arrayTy(intSort, intSort);

  Expr aInt = intConst("aInt", efac);
  Expr bInt = intConst("bInt", efac);

  Expr aBool = boolConst("aBool", efac);
  Expr bBool = boolConst("bBool", efac);

  Expr aAr1 = bind::mkConst(mkTerm<std::string>("aAr", efac), arraySort1);

  std::vector<Expr> e;
  Expr temp;
  std::vector<Expr> error;
  Expr tempError;

  tempError = array::select(aAr1, aBool); // aBool is wrong type, should be int
  error.push_back(tempError);
  e.push_back(error.back());

  tempError =
      array::store(aInt, bInt, bInt); // aInt is wrong type, should be an array
  error.push_back(tempError);
  e.push_back(error.back());

  tempError = array::select(array::constArray(intSort, aBool), aBool);
  // wrong type: the const array has index type int, not bool
  error.push_back(tempError);
  temp = mk<PLUS>(bInt, error.back(), aInt);
  e.push_back(temp);

  tempError =
      array::aDefault(aInt); // wrong type of argument, should be an array
  error.push_back(tempError);
  e.push_back(error.back());

  tempError =
      array::select(array::constArray(boolSort, aBool),
                    array::aDefault(aAr1)); // wrong type: constArray has bool
                                            // domain, but aDefault is int type
  error.push_back(tempError);
  e.push_back(error.back());

  checkNotWellFormed(e, error);
}

TEST_CASE("structWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr aBool = boolConst("aBool", efac);
  Expr bBool = boolConst("bBool", efac);

  Expr aInt = intConst("aInt", efac);
  Expr bInt = intConst("bInt", efac);

  Expr boolSort = sort::boolTy(efac);
  Expr intSort = sort::intTy(efac);

  Expr structSort = sort::structTy(boolSort, intSort);

  std::vector<Expr> e;
  Expr temp;

  temp = strct::mk(aBool, aInt);
  e.push_back(temp);

  temp = strct::mk(mk<GT>(aInt, bInt), mk<MOD>(aInt, aInt));
  e.push_back(temp);

  checkWellFormed(e, structSort);
  e.clear();

  temp = strct::insertVal(mk<AND>(aBool, bBool), 1, aBool);
  e.push_back(temp);

  temp = strct::insertVal(e.back(), 0, mk<EQ>(aBool, aBool));
  e.push_back(temp);

  temp = mk<ANY_TY>(aBool, bBool, aInt);
  temp = strct::extractVal(temp, 1);
  e.push_back(temp);

  checkWellFormed(e, boolSort);
  e.clear();
}

TEST_CASE("structNotWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr aBool = boolConst("aBool", efac);
  Expr bBool = boolConst("bBool", efac);

  Expr aInt = intConst("aInt", efac);
  Expr bInt = intConst("bInt", efac);

  Expr boolSort = sort::boolTy(efac);
  Expr intSort = sort::intTy(efac);

  Expr structSort = sort::structTy(boolSort, intSort);

  std::vector<Expr> e;
  Expr temp;
  std::vector<Expr> error;
  Expr tempError;

  tempError = mk<PLUS>(aInt);
  error.push_back(tempError);
  temp = strct::mk(error.back(), aBool);
  e.push_back(temp);

  tempError =
      strct::insertVal(mk<XOR>(aBool, bBool), 2, aBool); // index too high
  error.push_back(tempError);
  temp = strct::mk(aBool, aInt, error.back());
  e.push_back(temp);

  tempError = mk<EQ>(
      bBool, bInt); // will get this after inserting bBool into (aInt, bInt)
  error.push_back(tempError);
  temp = strct::insertVal(mk<EQ>(aInt, bInt), 0,
                          bBool); // bBool is wrong type, should be int
  e.push_back(tempError);

  tempError = strct::extractVal(mk<ANY_TY>(aBool, bBool), 2); // index too high
  error.push_back(tempError);
  e.push_back(tempError);

  tempError =
      mk<EXTRACT_VALUE>(mk<ANY_TY>(aInt), aInt); // a int is wrong argument type

  checkNotWellFormed(e, error);
}
TEST_CASE("gateWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr x = boolConst("x", efac);
  Expr y = boolConst("y", efac);
  Expr z = boolConst("z", efac);

  Expr t = mk<TRUE>(efac);
  Expr f = mk<FALSE>(efac);

  Expr boolSort = sort::boolTy(efac);

  std::vector<Expr> e;
  Expr temp;

  temp = gate::land(gate::lneg(x), f);
  e.push_back(temp);

  temp = gate::lor(x, boolop::lor(x, t));
  e.push_back(temp);

  ExprVector args (e.begin(), e.end());
  temp = mknary<OUT_G>(args);

  checkWellFormed(e, boolSort);
}
TEST_CASE("gateNotWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr x = boolConst("x", efac);
  Expr y = boolConst("y", efac);
  Expr z = boolConst("z", efac);

  Expr aInt = intConst("xInt", efac);

  Expr t = mk<TRUE>(efac);
  Expr f = mk<FALSE>(efac);

  Expr boolSort = sort::boolTy(efac);

  std::vector<Expr> e;
  Expr temp;
  std::vector<Expr> error;
  Expr tempError;

  tempError = gate::lneg(aInt);
  error.push_back(tempError);
  e.push_back(gate::lor(tempError, y));

  tempError = mk<AND_G>(x);
  error.push_back(tempError);
  e.push_back(tempError);

  tempError = mk<NEG_G>(x, y);
  error.push_back(tempError);
  e.push_back(tempError);

  tempError = mk<OUT_G>(aInt);
  error.push_back(tempError);
  e.push_back(tempError);

  checkNotWellFormed(e, error);
}
TEST_CASE("quantifierWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr aBool = boolConst("aBool", efac);
  Expr bBool = boolConst("bBool", efac);

  Expr aUnint = unintConst("aUnint", efac);
  Expr bUnint = unintConst("bUnint", efac);

  Expr t = mk<TRUE>(efac);
  Expr f = mk<FALSE>(efac);

  Expr boolSort = sort::boolTy(efac);
  Expr unintSort = sort::unintTy(efac);

  std::vector<Expr> e;
  Expr temp;
  Expr body;

  body = mk<EQ>(aUnint, bUnint);
  temp = mk<FORALL>(aUnint, bUnint, body);
  e.push_back(temp);

  body = boolop::limp(aBool, bBool);
 temp = mk<EXISTS>(aBool, bBool, body);
   e.push_back(temp);

  checkWellFormed(e, boolSort);
}
TEST_CASE("quantifierNotWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr aBool = boolConst("aBool", efac);
  Expr bBool = boolConst("bBool", efac);

  Expr aUnint = unintConst("aUnint", efac);
  Expr bUnint = unintConst("bUnint", efac);

  Expr t = mk<TRUE>(efac);
  Expr f = mk<FALSE>(efac);

  Expr boolSort = sort::boolTy(efac);
  Expr unintSort = sort::unintTy(efac);

  std::vector<Expr> e;
  Expr temp;
  std::vector<Expr> error;
  Expr tempError;
  Expr body;

  tempError = mk<EQ>(aUnint, bBool); // mismatching types
  error.push_back(tempError);
  body = tempError;
  temp = mk<FORALL>(aUnint, bUnint, body);
  e.push_back(temp);

 tempError = mk<EXISTS>(aBool, bBool, aUnint); // body is not bool type
  error.push_back(tempError);
  e.push_back(tempError);

  body = mk<EQ>(aUnint, bUnint);
  tempError = mk<FORALL>(aUnint, bBool, body); // bUnint in the body is not bound by the quantifier
  error.push_back(tempError);
  e.push_back(tempError);

  checkNotWellFormed(e, error);
}
TEST_CASE("lambdaWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr aBool = boolConst("aBool", efac);
  Expr bBool = boolConst("bBool", efac);

  Expr aUnint = unintConst("aUnint", efac);
  Expr bUnint = unintConst("bUnint", efac);

  Expr boolSort = sort::boolTy(efac);
  Expr unintSort = sort::unintTy(efac);

  Expr arraySort = mk<ARRAY_TY>(boolSort, unintSort, unintSort);

  std::vector<Expr> e;
  Expr temp;
  Expr body;

  body = mk<PLUS>(aUnint, aUnint);
  temp = mk<LAMBDA>(aBool, aUnint, body);
  e.push_back(temp);

  checkWellFormed(e, arraySort);
  e.clear();

  ExprVector sorts = {boolSort, unintSort, unintSort, boolSort};
  Expr arraySort2 = mknary<ARRAY_TY>(sorts);

  body = mk<AND>(mk<GT>(aUnint, bUnint), aBool);
  ExprVector args = {aBool, aUnint, bUnint, body};
  temp = mknary<LAMBDA>(args);
  e.push_back(temp);

  checkWellFormed(e, arraySort2);
}
TEST_CASE("lambdaNotWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr aBool = boolConst("aBool", efac);
  Expr bBool = boolConst("bBool", efac);

  Expr aUnint = unintConst("aUnint", efac);
  Expr bUnint = unintConst("bUnint", efac);

  Expr boolSort = sort::boolTy(efac);
  Expr unintSort = sort::unintTy(efac);

  std::vector<Expr> e;
  Expr temp;
  std::vector<Expr> error;
  Expr tempError;
  Expr body;

  body = mk <IFF>(aBool, bBool);
  tempError = mk<LAMBDA>(aBool, body); // bBool is not bound
  error.push_back(tempError);
  e.push_back(tempError);

  tempError = mk<LAMBDA>(aUnint); // not enough arguments
  error.push_back(tempError);
  e.push_back(tempError);

  checkNotWellFormed(e, error);
}