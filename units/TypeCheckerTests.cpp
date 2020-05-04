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

  e = boolop::lor(z, e);
  llvm::errs() << *e;

  TypeChecker tc;
  Expr ty = tc.typeOf(e);
  if (ty)
    llvm::errs() << "Type is " << *ty << "\n";
  else
    llvm::errs() << "Not well-formed expression. Type inference failed\n";
}
