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

#include "seahorn/Support/SeaDebug.h"

using namespace expr;
using namespace llvm;

Expr boolConst(const std::string &n, ExprFactory &efac) {
  return bind::boolConst(mkTerm<std::string>(n, efac));
}

Expr intConst(const std::string &n, ExprFactory &efac) {
  return bind::intConst(mkTerm<std::string>(n, efac));
}

Expr boolVar(const std::string &n, ExprFactory &efac) {
  return bind::boolVar(mkTerm<std::string>(n, efac));
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

  Expr a = boolVar("a", efac);
  Expr b = boolVar("b", efac);

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

  e[3] = mk<ITE>(a, x, mk<XOR>(b, y));

  e[4] = boolop::limp(mk<TRUE>(efac), mk<FALSE>(efac));

  TypeChecker tc;

  for (int i = 0; i < size; i++) {
    llvm::errs() << "Expression: " << *e[i] << "\n";
    Expr ty = tc.typeOf(e[i]);

    CHECK(ty == boolSort);
    if (ty)
      llvm::errs() << "Type is " << *ty << "\n\n";
    else
      llvm::errs() << "Not well-formed expression. Type inference failed\n";
  }
}
TEST_CASE("notWellFormed.test") {
  seahorn::SeaEnableLog("tc");
  ExprFactory efac;

  Expr xInt = intConst("intX", efac); // variable of type int

  Expr yBool = boolConst("yBool", efac);
  Expr aBool = boolConst("aBool", efac);
  Expr zBool = boolVar("zBool", efac);

  Expr temp;
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

  TypeChecker tc;

  for (int i = 0; i < size; i++) {
    llvm::errs() << "Expression: " << *e[i] << "\n";
    Expr ty = tc.typeOf(e[i]);

    CHECK(!ty);
    CHECK(tc.getNotWellFormed() == error[i]);
    if (ty)
      llvm::errs() << "Type is " << *ty << "\n\n";
    else
      llvm::errs() << "Not well-formed expression. Type inference failed\n";
  }
}