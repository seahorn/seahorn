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
#include "seahorn/Expr/TypeChecker.hh"
#include "seahorn/Expr/ExprOpBv.hh"

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

void checkNotWellFormed(Expr e[], Expr error[], int size) {
  Expr errorSort = sort::errorTy(e[0]->efac());
  TypeChecker tc;

  for (int i = 0; i < size; i++) {
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

void checkWellFormed(Expr e[], int size, Expr type) {
  TypeChecker tc;

  for (int i = 0; i < size; i++) {
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

  Expr boolSort = sort::boolTy(efac);

  int size = 5;
  Expr e[size];

  // e[0] = (!x && y)|| (x || z)
  e[0] = boolop::land(boolop::lneg(x), y);
  e[0] = boolop::lor(e[0], boolop::lor(x, z));

  // e[1] = !(x -> y) && z
  e[1] = boolop::lneg(boolop::limp(x, y));
  e[1] = boolop::land(e[1], z);

  // e[2] =  ((!x && y)|| (x || z)) <-> (!(x -> y) && z )
  e[2] = mk<IFF>(e[0], e[1]);

  e[3] = mk<ITE>(y, x, mk<XOR>(x, y));

  e[4] = boolop::limp(mk<TRUE>(efac), mk<FALSE>(efac));

  checkWellFormed(e, size, boolSort);
}
TEST_CASE("notWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  ExprFactory efac;

  Expr xInt = intConst("intX", efac); // variable of type int

  Expr yBool = boolConst("yBool", efac);
  Expr aBool = boolConst("aBool", efac);
  Expr zBool = boolConst("zBool", efac);

  Expr errorSort = sort::errorTy(efac);

  int size = 3;
  Expr e[size];
  Expr error[size];

  // yBool && (zBool && xInt)
  error[0] = boolop::land(zBool, xInt);
  e[0] = boolop::land(yBool, error[0]);

  // (yBool -> zBool) -> !xInt
  error[1] = boolop::lneg(xInt);
  e[1] = boolop::limp(boolop::limp(yBool, zBool), error[1]);

  // (zBool || xInt ) && (yBool -> zBool)
  error[2] = boolop::lor(zBool, xInt);
  e[2] = boolop::land(error[2], boolop::limp(yBool, zBool));

  checkNotWellFormed(e, error, size);
}

TEST_CASE("intWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

  Expr x = intConst("x", efac);
  Expr y = intConst("y", efac);
  Expr z = intConst("z", efac);

  Expr intSort = sort::intTy(efac);

  int size = 2;
  Expr e[size];
  Expr temp;

  e[0] = mk<PLUS>(x, y, z);

  e[1] = mk<PLUS>(mk<MINUS>(x, y), y, z);

  TypeChecker tc;

  checkWellFormed(e, size, intSort);
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

  int size = 2;
  Expr e[size];

  // e[0] = (aReal / bReal) * aReal * (aReal - bReal)
  e[0] = mk<MULT>(mk<DIV>(aReal, bReal), aReal, mk<UN_MINUS>(aReal, bReal));

  // e[1] = abs ((aReal / bReal) * aReal * (aReal - bReal)) % cReal
  e[1] = mk<REM>(mk<ABS>(e[0]), aReal);

  checkWellFormed(e, size, realSort);
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

  int size = 2;
  Expr e[size];

  // e[0] = aUnint mod (bUnint / cUnint)
  e[0] = mk<MOD>(aUnint, mk<IDIV>(bUnint, cUnint));

  // e[1] =  aUnint - (aUnint * cUnint) - (aUnint * cUnint)
  e[1] =
      mk<UN_MINUS>(aUnint, mk<MULT>(aUnint, cUnint), mk<MULT>(aUnint, cUnint));

  checkWellFormed(e, size, unintSort);
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

  int size = 3;
  Expr e[size];
  Expr error[size];

  e[0] = mk<ABS>(eBool);
  error[0] = e[0];

  e[1] = mk<ABS>(aInt, bInt);
  error[1] = e[1];

  e[2] = mk<DIV>(dUnint, mk<PLUS>(cReal, cReal), mk<MULT>(dUnint, dUnint));
  error[2] = e[2];

  checkNotWellFormed(e, error, size);
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

  int size = 4;
  Expr e[size];

  // (xBool && yBool && !xBool)= yBool
  e[0] = mk<EQ>(mk<AND>(xBool, yBool, mk<NEG>(xBool)), yBool);

  // ((xInt-yInt)+ yInt) <= abs(zInt)
  e[1] = mk<LEQ>(mk<PLUS>(mk<MINUS>(xInt, yInt), yInt), mk<ABS>(zInt));

  // (xReal >= yReal) != xBool
  e[2] = mk<NEQ>(mk<GEQ>(xReal, yReal), xBool);

  //  (xReal mod yReal ) < xRreal
  e[3] = mk<LT>(mk<MOD>(xReal, yReal), xReal);

  checkWellFormed(e, size, boolSort);
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

  int size = 4;
  Expr e[size];
  Expr error[size];

  error[0] = mk<LT>(xBool, yBool);

  // xBool && (xBool < yBool )
  e[0] = mk<AND>(xBool, error[0]);

  error[1] = mk<GEQ>(xReal, xReal, yReal);

  // yBool != [>=(xReal, xReal, yReal)]
  e[1] = mk<NEQ>(yBool, error[1]);

  error[2] = mk<EQ>(xReal, xInt);

  // ((xReal == xInt) > xReal )|| yBool
  e[2] = mk<OR>(mk<GT>(error[2], xReal), yBool);

  error[3] = mk<EQ>(mk<IMPL>(xBool, yBool), xReal);

  // (xBool -> yBool ) == xReal
  e[3] = error[3];

  checkNotWellFormed(e, error, size);
}
TEST_CASE("bvWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  // -- manages expressions
  ExprFactory efac;

Expr aInt = intConst ("aInt", efac);

Expr bvSort = bv::bvsort(10, efac);
Expr bvSort5 = bv::bvsort(5, efac);

Expr a10 = bvConst ("a10", efac, 10);
Expr b10 = bvConst ("b10", efac, 10);
Expr c10 = bvConst ("c10", efac, 10);
// Expr d10 = bv::bvnum(aInt, bvSort); //TODO

Expr a5 = bvConst ("a5", efac, 5);
Expr b5 = bvConst ("b5", efac, 5);
Expr c5 = bvConst ("c5", efac, 5);

int size = 6;
  Expr e[size];

  e[0] = mk<BNOT>(mk<BOR>(a10,b10));

  e[1] = mk <BAND>(mk<BREDAND>(a10), b10);

  e[2] = mk <BREDOR>(mk<BXNOR> (mk<BNEG>(a10), mk<BOR>(b10,c10)));

  e[3] = mk <BSUB>(mk<BCONCAT>(a5, b5), a10);

  e[4] = mk <BADD>(mk<BNAND>(a10, b10), mk<BSHL>(c10, c10));

  e[5] = mk<BSHL> (bv::sext(a5, 5), a10);

  checkWellFormed(e, size, bvSort);

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

Expr a10 = bvConst ("a10", efac, 10);
Expr b10 = bvConst ("b10", efac, 10);
Expr c10 = bvConst ("c10", efac, 10);

Expr a7 = bvConst ("a7", efac, 7);

Expr a5 = bvConst ("a5", efac, 5);
Expr b5 = bvConst ("b5", efac, 5);
Expr c5 = bvConst ("c5", efac, 5);

int size = 11;
Expr e[size];
Expr error[size];

error[0] = mk<BNOT> (a10, a10); //too many arguments: Unary
e[0] = error[0];

error [1] = mk <BREDAND>(aInt); // wrong type of argument Unary
e[1] = mk<BMUL>(mk<BSLE>(error[1], a10), b10);

error [2] = mk <BSDIV> (a10); // not enough arguments Nary
e[2] = mk<BSGT>(error[2], a10);

error [3] = mk <BSGT> (a10, aUnint); // wrong type of argument: Nary
e[3] = mk<BSHL>(b10, error[3]);

error [4] =  mk <BASHR>(a5);//not enough arguments : binary
e[4] = error[4];

error [5] = mk <BSHL>(a10, b10, c10); //too many arguments : binary
e[5] = mk<BNAND>(a10, mk<BREDOR>(error[5]));

error [6] =  mk<BCONCAT>(a7);//not enough arguments : concat
e[6] = error[6];//mk<BCONCAT>(error[6], a3);

error [7] = mk <BCONCAT>(a5, aReal);//wrong type of arugment 
e[7] = mk<BNOT>(error[7]);

error[8] = mk<BUGT>(a10, mk<BCONCAT>(a5, a10)); //widths do not match
e[8] = error[8];

error[9] = mk<BSEXT>(a10, b10); // should be {bv, bvsort}
e[9] = mk<BCONCAT>(error[9], a5);

error[10] = mk<BSEXT>(a10, bvSort, b10);
e[10] = error[10];
checkNotWellFormed(e,error, size);
}